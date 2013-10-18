{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE QuasiQuotes #-}

-- |
-- Module      : Data.Array.Accelerate.C.Exp
-- Copyright   : [2009..2013] Manuel M T Chakravarty, Gabriele Keller, Trevor L. McDonell

-- License     : BSD3
--
-- Maintainer  : Manuel M T Chakravarty <chak@cse.unsw.edu.au>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--
-- This module implements the C code generation for scalar Accelerate expressions.
--

module Data.Array.Accelerate.C.Exp (
  expToC
) where

  -- standard libraries
import Data.Char  
import Data.Int
import Prelude

  -- libraries
import Data.Loc
import qualified 
       Language.C         as C
import Language.C.Quote.C as C

  -- accelerate
import Data.Array.Accelerate.Array.Sugar
import Data.Array.Accelerate.Array.Representation               ( SliceIndex(..) )
import Data.Array.Accelerate.AST
import Data.Array.Accelerate.Tuple
import Data.Array.Accelerate.Type
import Data.Array.Accelerate.Prelude as Prl

  -- friends
import Data.Array.Accelerate.C.Base
import Data.Array.Accelerate.C.Type
import qualified Data.Array.Accelerate.Analysis.Type    as Sugar

-- Generating C code from scalar Accelerate expressions
-- ----------------------------------------------------

-- Produces a list of expression whose length corresponds to the number of tuple components of the result type.
--
expToC :: Elt t => Exp () t -> [C.Exp]
expToC x = expToCOpen x

expToCOpen :: Elt t => OpenExp env aenv t -> [C.Exp]
expToCOpen x = case x of
    (PrimConst xc) -> [primConstToC xc]
    (Const xc) -> constToC (Sugar.expType(x)) xc
    (PrimApp f arg) -> [primToC f (expToCOpen arg)]
    (Tuple xc) -> tupToC xc
    (Prj i t) -> prjToC i t x
    --(Cond p t e) -> condToC p t e
    --(While p f x) -> whileToC p f x
    
    -- Shapes and indices
    (IndexNil) -> []
    (IndexAny) -> []
    (IndexCons sh sz) -> (expToCOpen sh) ++ (expToCOpen sz)
    (IndexHead ix) -> return . last $ expToCOpen ix
    (IndexTail ix) ->          init $ expToCOpen ix
    (IndexSlice ix slix sh) -> indexSlice ix slix sh
    (IndexFull  ix slix sl) -> indexFull  ix slix sl
    (ToIndex sh ix) -> toIndexC   sh ix
    --(FromIndex sh ix) -> fromIndex sh ix env

    _ -> error $ "Not implemented." ++ (show $ x)



-- Restrict indices based on a slice specification. In the SliceAll case we
    -- elide the presence of IndexAny from the head of slx, as this is not
-- represented in by any C term (Any ~ [])
--
indexSlice :: (Elt slix, Elt sh) => SliceIndex (EltRepr slix) sl co (EltRepr sh)
           -> OpenExp env aenv slix
           -> OpenExp env aenv sh
           -> [C.Exp]
indexSlice sliceIndex slix sh =
  let restrict :: SliceIndex slix sl co sh -> [C.Exp] -> [C.Exp] -> [C.Exp]
      restrict SliceNil              _       _       = []
      restrict (SliceAll   sliceIdx) slx     (sz:sl) = sz : restrict sliceIdx slx sl
      restrict (SliceFixed sliceIdx) (_:slx) ( _:sl) =      restrict sliceIdx slx sl
      restrict _ _ _ = error "IndexSlice" "unexpected shapes"
      --
      slice slix' sh' = reverse $ restrict sliceIndex (reverse slix') (reverse sh')
  in
  slice (expToCOpen slix) ( expToCOpen sh )

-- Extend indices based on a slice specification. In the SliceAll case we
-- elide the presence of Any from the head of slx.
--
indexFull :: (Elt slix, Elt sl) => SliceIndex (EltRepr slix) (EltRepr sl) co sh
          -> OpenExp env aenv slix
          -> OpenExp env aenv sl
          -> [C.Exp]
indexFull sliceIndex slix sl =
  let extend :: SliceIndex slix sl co sh -> [C.Exp] -> [C.Exp] -> [C.Exp]
      extend SliceNil              _        _       = []
      extend (SliceAll   sliceIdx) slx      (sz:sh) = sz : extend sliceIdx slx sh
      extend (SliceFixed sliceIdx) (sz:slx) sh      = sz : extend sliceIdx slx sh
      extend _ _ _ = error "IndexFull" "unexpected shapes"
      --
      replicate slix' sl' = reverse $ extend sliceIndex (reverse slix') (reverse sl')
  in
  replicate(expToCOpen slix) (expToCOpen sl)

-- Convert between linear and multidimensional indices. For the
-- multidimensional case, we've inlined the definition of 'fromIndex'
-- because we need to return an expression for each component.
-- Src: Accel-CUDA CodeGen.hs
-- 
toIndexC :: Elt sh => OpenExp env aenv sh -> OpenExp env aenv sh  -> [C.Exp]
toIndexC sh ix = [ ccall "toIndex" [ ccall "shape" sh', ccall "shape" ix' ] ]
    where
      sh'   = expToCOpen sh
      ix'   = expToCOpen ix

--fromIndexC :: OpenExp env aenv sh -> OpenExp env aenv Int -> [C.Exp]
--fromIndexC sh ix = reverse $ fromIndexC' (reverse sh') (single "fromIndex" ix')
--    where
--      sh'   = expToCOpen sh
--      ix'   = expToCOpen ix

--fromIndexC' :: [C.Exp] -> C.Exp -> [C.Exp]
--fromIndexC' []     _     = []
--fromIndexC' [_]    i     = [i]
--fromIndexC' (d:ds) i     = [cexp| $exp:i' % $exp:d |] : ds'
--    where
--        i'    = bind [cty| int |] i
--        ds'   = fromIndex' ds [cexp| $exp:i' / $exp:d |]

-- Some terms demand we extract only singly typed expressions
--
single :: String -> [C.Exp] -> C.Exp
single _   [x] = x
single loc _   = error "expected single expression"

-- Tuples
-- ------

-- Convert an open expression into a sequence of C expressions. We retain
-- snoc-list ordering, so the element at tuple index zero is at the end of
-- the list. Note that nested tuple structures are flattened.
-- Src: Accel-CUDA CodeGen.hs
--
tupToC :: Tuple (OpenExp env aenv) t -> [C.Exp]
tupToC tup =
  case tup of
    NilTup          -> []
    SnocTup t e     -> (tupToC t) ++ (expToCOpen e)

-- Project out a tuple index. Since the nested tuple structure is flattened,
-- this actually corresponds to slicing out a subset of the list of C
-- expressions, rather than picking out a single element.
-- Src: Accel-CUDA CodeGen.hs
--
prjToC :: forall aenv env t e.  Elt t => TupleIdx (TupleRepr t) e
     -> OpenExp env aenv t
     -> OpenExp env aenv e
     -> [C.Exp]
prjToC ix t e =
  let subset = reverse
             . take (length      $ expType_ e)
             . drop (prjToInt ix $ Sugar.preExpType Sugar.accType t)
             . reverse
  in
  subset $ expToCOpen t

-- Convert a tuple index into the corresponding integer. Since the internal
-- representation is flat, be sure to walk over all sub components when indexing
-- past nested tuples.
--
prjToInt :: TupleIdx t e -> TupleType a -> Int
prjToInt ZeroTupIdx     _                 = 0
prjToInt (SuccTupIdx i) (b `PairTuple` a) = sizeTupleType a + prjToInt i b
prjToInt _              _                 = error "D.A.A.C.Exp.prjToInt: inconsistent valuation"

sizeTupleType :: TupleType a -> Int
sizeTupleType UnitTuple       = 0
sizeTupleType (SingleTuple _) = 1
sizeTupleType (PairTuple a b) = sizeTupleType a + sizeTupleType b

expType_ :: OpenExp aenv env t -> [C.Type]
expType_ = tupleTypeToC . Sugar.preExpType Sugar.accType

-- Primtive functions
-- ------------------

primToC :: PrimFun p -> [C.Exp] -> C.Exp
primToC (PrimAdd              _) [a,b] = [cexp|$exp:a + $exp:b|]
primToC (PrimSub              _) [a,b] = [cexp|$exp:a - $exp:b|]
primToC (PrimMul              _) [a,b] = [cexp|$exp:a * $exp:b|]
primToC (PrimNeg              _) [a]   = [cexp| - $exp:a|]
primToC (PrimAbs             ty) [a]   = absToC ty a
primToC (PrimSig             ty) [a]   = sigToC ty a
primToC (PrimQuot             _) [a,b] = [cexp|$exp:a / $exp:b|]
primToC (PrimRem              _) [a,b] = [cexp|$exp:a % $exp:b|]
primToC (PrimIDiv            ty) [a,b] = ccall "idiv" [ccast (NumScalarType $ IntegralNumType ty) a,
                                                       ccast (NumScalarType $ IntegralNumType ty) b]
primToC (PrimMod             ty) [a,b] = ccall "mod"  [ccast (NumScalarType $ IntegralNumType ty) a,
                                                       ccast (NumScalarType $ IntegralNumType ty) b]
primToC (PrimBAnd             _) [a,b] = [cexp|$exp:a & $exp:b|]
primToC (PrimBOr              _) [a,b] = [cexp|$exp:a | $exp:b|]
primToC (PrimBXor             _) [a,b] = [cexp|$exp:a ^ $exp:b|]
primToC (PrimBNot             _) [a]   = [cexp|~ $exp:a|]
primToC (PrimBShiftL          _) [a,b] = [cexp|$exp:a << $exp:b|]
primToC (PrimBShiftR          _) [a,b] = [cexp|$exp:a >> $exp:b|]
primToC (PrimBRotateL         _) [a,b] = ccall "rotateL" [a,b]
primToC (PrimBRotateR         _) [a,b] = ccall "rotateR" [a,b]
primToC (PrimFDiv             _) [a,b] = [cexp|$exp:a / $exp:b|]
primToC (PrimRecip           ty) [a]   = recipToC ty a
primToC (PrimSin             ty) [a]   = ccall (FloatingNumType ty `postfix` "sin")   [a]
primToC (PrimCos             ty) [a]   = ccall (FloatingNumType ty `postfix` "cos")   [a]
primToC (PrimTan             ty) [a]   = ccall (FloatingNumType ty `postfix` "tan")   [a]
primToC (PrimAsin            ty) [a]   = ccall (FloatingNumType ty `postfix` "asin")  [a]
primToC (PrimAcos            ty) [a]   = ccall (FloatingNumType ty `postfix` "acos")  [a]
primToC (PrimAtan            ty) [a]   = ccall (FloatingNumType ty `postfix` "atan")  [a]
primToC (PrimAsinh           ty) [a]   = ccall (FloatingNumType ty `postfix` "asinh") [a]
primToC (PrimAcosh           ty) [a]   = ccall (FloatingNumType ty `postfix` "acosh") [a]
primToC (PrimAtanh           ty) [a]   = ccall (FloatingNumType ty `postfix` "atanh") [a]
primToC (PrimExpFloating     ty) [a]   = ccall (FloatingNumType ty `postfix` "exp")   [a]
primToC (PrimSqrt            ty) [a]   = ccall (FloatingNumType ty `postfix` "sqrt")  [a]
primToC (PrimLog             ty) [a]   = ccall (FloatingNumType ty `postfix` "log")   [a]
primToC (PrimFPow            ty) [a,b] = ccall (FloatingNumType ty `postfix` "pow")   [a,b]
primToC (PrimLogBase         ty) [a,b] = logBaseToC ty a b
primToC (PrimTruncate     ta tb) [a]   = truncateToC ta tb a
primToC (PrimRound        ta tb) [a]   = roundToC ta tb a
primToC (PrimFloor        ta tb) [a]   = floorToC ta tb a
primToC (PrimCeiling      ta tb) [a]   = ceilingToC ta tb a
primToC (PrimAtan2           ty) [a,b] = ccall (FloatingNumType ty `postfix` "atan2") [a,b]
primToC (PrimLt               _) [a,b] = [cexp|$exp:a < $exp:b|]
primToC (PrimGt               _) [a,b] = [cexp|$exp:a > $exp:b|]
primToC (PrimLtEq             _) [a,b] = [cexp|$exp:a <= $exp:b|]
primToC (PrimGtEq             _) [a,b] = [cexp|$exp:a >= $exp:b|]
primToC (PrimEq               _) [a,b] = [cexp|$exp:a == $exp:b|]
primToC (PrimNEq              _) [a,b] = [cexp|$exp:a != $exp:b|]
primToC (PrimMax             ty) [a,b] = maxToC ty a b
primToC (PrimMin             ty) [a,b] = minToC ty a b
primToC PrimLAnd                 [a,b] = [cexp|$exp:a && $exp:b|]
primToC PrimLOr                  [a,b] = [cexp|$exp:a || $exp:b|]
primToC PrimLNot                 [a]   = [cexp| ! $exp:a|]
primToC PrimOrd                  [a]   = ordToC a
primToC PrimChr                  [a]   = chrToC a
primToC PrimBoolToInt            [a]   = boolToIntToC a
primToC (PrimFromIntegral ta tb) [a]   = fromIntegralToC ta tb a
primToC _ _ = -- If the argument lists are not the correct length
  error "D.A.A.C.Exp.codegenPrim: inconsistent valuation"

-- Constants and numeric types
-- ---------------------------
 
constToC :: TupleType a -> a -> [C.Exp]
constToC UnitTuple           _      = []
constToC (SingleTuple ty)    c      = [scalarToC ty c]
constToC (PairTuple ty1 ty0) (cs,c) = constToC ty1 cs ++ constToC ty0 c

scalarToC :: ScalarType a -> a -> C.Exp
scalarToC (NumScalarType    ty) = numScalarToC ty
scalarToC (NonNumScalarType ty) = nonNumScalarToC ty

numScalarToC :: NumType a -> a -> C.Exp
numScalarToC (IntegralNumType ty) = integralScalarToC ty
numScalarToC (FloatingNumType ty) = floatingScalarToC ty

integralScalarToC :: IntegralType a -> a -> C.Exp
integralScalarToC ty x | IntegralDict <- integralDict ty = [cexp| ( $ty:(integralTypeToC ty) ) $exp:(cintegral x) |]

floatingScalarToC :: FloatingType a -> a -> C.Exp
floatingScalarToC (TypeFloat   _) x = C.Const (C.FloatConst (shows x "f") (toRational x) noLoc) noLoc
floatingScalarToC (TypeCFloat  _) x = C.Const (C.FloatConst (shows x "f") (toRational x) noLoc) noLoc
floatingScalarToC (TypeDouble  _) x = C.Const (C.DoubleConst (show x) (toRational x) noLoc) noLoc
floatingScalarToC (TypeCDouble _) x = C.Const (C.DoubleConst (show x) (toRational x) noLoc) noLoc

nonNumScalarToC :: NonNumType a -> a -> C.Exp
nonNumScalarToC (TypeBool   _) x = cbool x
nonNumScalarToC (TypeChar   _) x = [cexp|$char:x|]
nonNumScalarToC (TypeCChar  _) x = [cexp|$char:(chr (fromIntegral x))|]
nonNumScalarToC (TypeCUChar _) x = [cexp|$char:(chr (fromIntegral x))|]
nonNumScalarToC (TypeCSChar _) x = [cexp|$char:(chr (fromIntegral x))|]

primConstToC :: PrimConst a -> C.Exp
primConstToC (PrimMinBound ty) = minBoundToC ty
primConstToC (PrimMaxBound ty) = maxBoundToC ty
primConstToC (PrimPi       ty) = piToC ty

piToC :: FloatingType a -> C.Exp
piToC ty | FloatingDict <- floatingDict ty = floatingScalarToC ty pi

minBoundToC :: BoundedType a -> C.Exp
minBoundToC (IntegralBoundedType ty) | IntegralDict <- integralDict ty = integralScalarToC ty minBound
minBoundToC (NonNumBoundedType   ty) | NonNumDict   <- nonNumDict   ty = nonNumScalarToC   ty minBound

maxBoundToC :: BoundedType a -> C.Exp
maxBoundToC (IntegralBoundedType ty) | IntegralDict <- integralDict ty = integralScalarToC ty maxBound
maxBoundToC (NonNumBoundedType   ty) | NonNumDict   <- nonNumDict   ty = nonNumScalarToC   ty maxBound


-- Methods from Num, Floating, Fractional and RealFrac
-- ---------------------------------------------------

absToC :: NumType a -> C.Exp -> C.Exp
absToC (FloatingNumType ty) x = ccall (FloatingNumType ty `postfix` "fabs") [x]
absToC (IntegralNumType ty) x =
  case ty of
    TypeWord _          -> x
    TypeWord8 _         -> x
    TypeWord16 _        -> x
    TypeWord32 _        -> x
    TypeWord64 _        -> x
    TypeCUShort _       -> x
    TypeCUInt _         -> x
    TypeCULong _        -> x
    TypeCULLong _       -> x
    _                   -> ccall "abs" [x]

sigToC :: NumType a -> C.Exp -> C.Exp
sigToC (IntegralNumType ty) = integralSigToC ty
sigToC (FloatingNumType ty) = floatingSigToC ty

integralSigToC :: IntegralType a -> C.Exp -> C.Exp
integralSigToC ty x = [cexp|$exp:x == $exp:zero ? $exp:zero : $exp:(ccall "copysign" [one,x]) |]
  where
    zero | IntegralDict <- integralDict ty = integralScalarToC ty 0
    one  | IntegralDict <- integralDict ty = integralScalarToC ty 1

floatingSigToC :: FloatingType a -> C.Exp -> C.Exp
floatingSigToC ty x = [cexp|$exp:x == $exp:zero ? $exp:zero : $exp:(ccall (FloatingNumType ty `postfix` "copysign") [one,x]) |]
  where
    zero | FloatingDict <- floatingDict ty = floatingScalarToC ty 0
    one  | FloatingDict <- floatingDict ty = floatingScalarToC ty 1


recipToC :: FloatingType a -> C.Exp -> C.Exp
recipToC ty x | FloatingDict <- floatingDict ty = [cexp|$exp:(floatingScalarToC ty 1) / $exp:x|]


logBaseToC :: FloatingType a -> C.Exp -> C.Exp -> C.Exp
logBaseToC ty x y = let a = ccall (FloatingNumType ty `postfix` "log") [x]
                        b = ccall (FloatingNumType ty `postfix` "log") [y]
                        in
                        [cexp|$exp:b / $exp:a|]


minToC :: ScalarType a -> C.Exp -> C.Exp -> C.Exp
minToC (NumScalarType ty@(IntegralNumType _)) a b = ccall (ty `postfix` "min")  [a,b]
minToC (NumScalarType ty@(FloatingNumType _)) a b = ccall (ty `postfix` "fmin") [a,b]
minToC (NonNumScalarType _)                   a b =
  let ty = scalarType :: ScalarType Int32
  in  minToC ty (ccast ty a) (ccast ty b)


maxToC :: ScalarType a -> C.Exp -> C.Exp -> C.Exp
maxToC (NumScalarType ty@(IntegralNumType _)) a b = ccall (ty `postfix` "max")  [a,b]
maxToC (NumScalarType ty@(FloatingNumType _)) a b = ccall (ty `postfix` "fmax") [a,b]
maxToC (NonNumScalarType _)                   a b =
  let ty = scalarType :: ScalarType Int32
  in  maxToC ty (ccast ty a) (ccast ty b)


-- Type coercions
--
ordToC :: C.Exp -> C.Exp
ordToC = ccast (scalarType :: ScalarType Int)

chrToC :: C.Exp -> C.Exp
chrToC = ccast (scalarType :: ScalarType Char)

boolToIntToC :: C.Exp -> C.Exp
boolToIntToC = ccast (scalarType :: ScalarType Int)

fromIntegralToC :: IntegralType a -> NumType b -> C.Exp -> C.Exp
fromIntegralToC _ ty = ccast (NumScalarType ty)

truncateToC :: FloatingType a -> IntegralType b -> C.Exp -> C.Exp
truncateToC ta tb x
  = ccast (NumScalarType (IntegralNumType tb))
  $ ccall (FloatingNumType ta `postfix` "trunc") [x]

roundToC :: FloatingType a -> IntegralType b -> C.Exp -> C.Exp
roundToC ta tb x
  = ccast (NumScalarType (IntegralNumType tb))
  $ ccall (FloatingNumType ta `postfix` "round") [x]

floorToC :: FloatingType a -> IntegralType b -> C.Exp -> C.Exp
floorToC ta tb x
  = ccast (NumScalarType (IntegralNumType tb))
  $ ccall (FloatingNumType ta `postfix` "floor") [x]

ceilingToC :: FloatingType a -> IntegralType b -> C.Exp -> C.Exp
ceilingToC ta tb x
  = ccast (NumScalarType (IntegralNumType tb))
  $ ccall (FloatingNumType ta `postfix` "ceil") [x]


-- Auxiliary Functions
-- -------------------

ccast :: ScalarType a -> C.Exp -> C.Exp
ccast ty x = [cexp|($ty:(scalarTypeToC ty)) $exp:x|]

postfix :: NumType a -> String -> String
postfix (FloatingNumType (TypeFloat  _)) x = x ++ "f"
postfix (FloatingNumType (TypeCFloat _)) x = x ++ "f"
postfix _                                x = x
