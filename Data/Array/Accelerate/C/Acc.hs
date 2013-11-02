{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE QuasiQuotes #-}

-- |
-- Module      : Data.Array.Accelerate.C.Acc
-- Copyright   : [2009..2013] Manuel M T Chakravarty, Gabriele Keller, Trevor L. McDonell

-- License     : BSD3
--
-- Maintainer  : Manuel M T Chakravarty <chak@cse.unsw.edu.au>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--
-- This module implements the C code generation for Accelerate array computations.
--

module Data.Array.Accelerate.C.Acc (
  accToC
) where

  -- libraries
import Data.List
import qualified 
       Language.C         as C
import Language.C.Quote.C as C

  -- accelerate
import Data.Array.Accelerate.Array.Sugar
import Data.Array.Accelerate.AST                  hiding (Val(..), prj)
import Data.Array.Accelerate.Analysis.Shape       hiding (accDim)
  -- friends
import Data.Array.Accelerate.C.Base
import Data.Array.Accelerate.C.Exp
import Data.Array.Accelerate.C.Type


-- Generating C code from Accelerate computations
-- ----------------------------------------------

-- Compile an open Accelerate computation into a function definition.
--
-- The computation may contain free array variables according to the array variable environment passed as a first argument.
--
accToC :: forall arrs aenv. Arrays arrs => Env aenv -> OpenAcc aenv arrs -> C.Definition

accToC aenv' (OpenAcc (Alet bnd body))
  = accToC aenv_bnd body
  where
    (_, aenv_bnd) = aenv' `pushAccEnv` bnd

accToC _aenv' (OpenAcc (Use _))
  = [cedecl| int dummy_declaration; |]

accToC aenv' acc@(OpenAcc (Map f arr))
  = [cedecl|
      void $id:cFunName ( $params:(cresParams ++ cenvParams ++ cargParams) )
      {
        const typename HsWord64 size = $exp:(csize (accDim arr) argSh);
        for (typename HsWord64 i = 0; i < size; i++)
        {
          $items:assigns
        }
      }
    |]
  where
    cresTys    = accTypeToC acc
    cresNames  = accNames "res" [length cresTys - 1]
    cresParams = [ [cparam| $ty:t $id:name |] | (t, name) <- zip cresTys cresNames]
    --
    cenvParams = aenvToCargs aenv'
    --
    cargTys    = accTypeToC arr
    cargNames  = accNames "arg" [length cargTys - 1]
    cargParams = [ [cparam| $ty:t $id:name |] | (t, name) <- zip cargTys cargNames]
    --
    argSh      = [cexp| * $id:(head cargNames) |]
    (bnds, es) = fun1ToC aenv' f 
    assigns    = [ [citem| {
                     const $ty:argTy $id:arg = $id:argArr [i]; 
                     $id:resArr [i] = $exp:e; 
                   } |] 
                 | (resArr, argArr, (argTy, arg), e) <- zip4 (tail cresNames) (tail cargNames)  -- head is the shape variable
                                                             bnds es
                 ]

accToC aenv' acc@(OpenAcc (ZipWith f arr1 arr2))
  = [cedecl|
      void $id:cFunName ( $params:(cresParams ++ cenvParams ++ cargParams1 ++ cargParams2) )
      {
        const typename HsWord64 size1 = $exp:(csize (accDim arr1) argSh1);
        const typename HsWord64 size2 = $exp:(csize (accDim arr2) argSh2);
        const typename HsWord64 size  = size1 >= size2 ? size1 : size2;
        for (typename HsWord64 i = 0; i < size; i++)
        {
          $items:assigns
          $items:assigns1
        }
      }
    |]
  where
    cresTys     = accTypeToC acc
    cresNames   = accNames "res" [length cresTys - 1]
    cresParams  = [ [cparam| $ty:t $id:name |] | (t, name) <- zip cresTys cresNames]
    --
    cenvParams  = aenvToCargs aenv'
    --
    cargTys1    = accTypeToC arr1
    cargTys2    = accTypeToC arr2
    cargNames1  = accNames "arg" [length cargTys1 - 1]
    cargNames2  = accNames "arg" [length cargTys2 - 1]
    cargParams1 = [ [cparam| $ty:t $id:name |] | (t, name) <- zip cargTys1 cargNames1]
    cargParams2 = [ [cparam| $ty:t $id:name |] | (t, name) <- zip cargTys2 cargNames2]
    --
    argSh1       = [cexp| * $id:(head cargNames1) |]
    argSh2       = [cexp| * $id:(head cargNames2) |]
    (bnds, es)  = fun2ToC aenv' f  
    assigns     = [ [citem| {
                     const $ty:argTy $id:arg = $id:argArr [i]; 
                     $id:resArr [i] = $exp:e; 
                   } |]
                 | (resArr, argArr, (argTy, arg), e)
                      <- zip4 (tail cresNames) (tail cargNames1) bnds es
                 ]
                 -- | (resArr, argArr, argArr2, (argTy, arg), e)
                 --     <- zip5 (tail cresNames) (tail cargNames1) (tail cargNames2) bnds es
    assigns1     = [ [citem| {
                     const $ty:argTy $id:arg = $id:argArr [i]; 
                     $id:resArr [i] = $exp:e; 
                   } |]
                 | (resArr, argArr, (argTy, arg), e)
                      <- zip4 (tail cresNames) (tail cargNames2) bnds es
                 ]

accToC aenv' acc@(OpenAcc (Generate _sh f))
  = [cedecl|
      void $id:cFunName ( $params:(cresParams ++ cenvParams) )
      {
        const typename HsWord64 size = $exp:(csize (accDim acc) accSh);
        for (typename HsWord64 i = 0; i < size; i++)
        {
          $items:assigns
        }
      }
    |]
  where
    cresTys    = accTypeToC acc
    cresNames  = accNames "res" [length cresTys - 1]
    cresParams = [ [cparam| $ty:t $id:name |] | (t, name) <- zip cresTys cresNames]
    --
    cenvParams = aenvToCargs aenv'
    --
    shName     = head cresNames
    accSh       = [cexp| * $id:shName |]    
    (bnds, es) = fun1ToC aenv' f 
    assigns    = [ [citem| const $ty:argTy $id:arg = $exp:d; |] 
                 | (d, (argTy, arg)) <- zip (fromIndexWithShape shName "i" (length bnds)) bnds
                 ]
                 ++
                 [ [citem| $id:resArr [i] = $exp:e; |] 
                 | (resArr, e) <- zip (tail cresNames) es             -- head is the shape variable
                 ]

--accToC aenv' acc@(OpenAcc (Generate sh e))
--  = [cedecl|
--      void $id:cFunName ( $params:(cresParams ++ cenvParams ++ cargParams) )
--      {
--        const typename HsWord64 size = $exp:(csize (accDim arr) argSh);
--        for (typename HsWord64 i = 0; i < size; i++)
--        {
--          $items:assigns
--        }
--      }
--    |]
--  where
--    cresTys    = accTypeToC acc
--    cresNames  = accNames "res" [length cresTys - 1]
--    cresParams = [ [cparam| $ty:t $id:name |] | (t, name) <- zip cresTys cresNames]
--    --
--    cenvParams = aenvToCargs aenv'
--    --
--    cargTys    = accTypeToC arr
--    cargNames  = accNames "arg" [length cargTys - 1]
--    cargParams = [ [cparam| $ty:t $id:name |] | (t, name) <- zip cargTys cargNames]
--    --
--    argSh      = [cexp| * $id:(head cargNames) |]
--    --(bnds, es) = fun1ToC aenv' f
--    assigns    = [ [citem| {
--                     const $ty:argTy $id:arg = $id:argArr [i]; 
--                     $id:resArr [i] = $exp:e; 
--                   } |] 
--                 | (resArr, argArr, (argTy, arg), e) <- zip4 (tail cresNames) (tail cargNames) bnds es
--                 ]

accToC _ _ = error "D.A.A.C.Acc: unimplemented"

--------------------------------------------------------------------------------------------------------------
--generate :: (Shape ix, Elt a) => Exp ix -> (Exp ix -> Exp a) -> Acc (Array ix a)

--Generate    :: (Shape sh, Elt e)
--            => PreExp     acc aenv sh                         -- output shape
--            -> PreFun     acc aenv (sh -> e)                  -- representation function
--            -> PreOpenAcc acc aenv (Array sh e)


--mkGenerate :: forall aenv sh e. (Shape sh, Elt e)
--    => DeviceProperties -> Env aenv -> fun1ToC aenv (sh -> e) -> [CUTranslSkel aenv (Array sh e)]
--mkGenerate dev aenv (CUFun1 _ f)
--  = return
--  $ CUTranslSkel "generate" [cunit|

--    --$esc:("#include <accelerate_cuda.h>")
--    $edecl:(cdim "DimOut" dim)
--    $edecls:texIn

--    --extern "C" __global__ void
--    generate
--    (
--        $params:argIn,
--        $params:argOut
--    )
--    {
--        const int shapeSize     = size(shOut);
--        const int gridSize      = $exp:(gridSize dev);
--              int ix;

--        for ( ix =  $exp:(threadIdx dev)
--            ; ix <  shapeSize
--            ; ix += gridSize )
--        {
--            const typename DimOut sh = fromIndex(shOut, ix);

--            $items:(setOut "ix" .=. f sh)
--        }
--    }
--  |]
--  where
--    dim                 = expDim (undefined :: Exp aenv sh)
--    sh                  = cshape dim (cvar "sh")
--    (texIn, argIn)      = environment dev aenv
--    (argOut, setOut)    = setters "Out" (undefined :: Array sh e)

--expDim :: forall acc env aenv sh. Elt sh => PreOpenExp acc env aenv sh -> Int
--expDim _ = ndim (eltType (undefined :: sh))

--ndim :: TupleType a -> Int
--ndim UnitTuple       = 0
--ndim (SingleTuple _) = 1
--ndim (PairTuple a b) = ndim a + ndim b

--setters :: forall sh e. (Shape sh, Elt e)
--    => Name                             -- group names
--    -> Array sh e                       -- dummy to fix types
--    -> ([C.Param], Name -> [C.Exp])
--setters grp _
--  = let (sh, arrs)      = namesOfArray grp (undefined :: e)
--        dim             = expDim (undefined :: Exp aenv sh)
--        sh'             = [cparam| const typename $id:("DIM" ++ show dim) $id:sh |]
--        arrs'           = zipWith (\t n -> [cparam| $ty:t * __restrict__ $id:n |]) (eltType (undefined :: e)) arrs
--    in
--    ( sh' : arrs'
--    , \ix -> map (\a -> [cexp| $id:a [ $id:ix ] |]) arrs
--    )

--environment :: forall aenv. DeviceProperties
--    -> Gamma aenv -> ([C.Definition], [C.Param])
--environment dev gamma@(Gamma aenv)
--  | computeCapability dev < Compute 2 0
--  = Map.foldrWithKey (\(Idx_ v) _ (ds,ps) -> let (d,p) = asTex v in (d++ds, p:ps)) ([],[]) aenv

--  | otherwise
--  = ([], Map.foldrWithKey (\(Idx_ v) _ vs -> asArg v ++ vs) [] aenv)

--  where
--    asTex :: forall sh e. (Shape sh, Elt e) => Idx aenv (Array sh e) -> ([C.Definition], C.Param)
--    asTex ix = arrayAsTex (undefined :: Array sh e) (groupOfAvar gamma ix)

--    asArg :: forall sh e. (Shape sh, Elt e) => Idx aenv (Array sh e) -> [C.Param]
--    asArg ix = arrayAsArg (undefined :: Array sh e) (groupOfAvar gamma ix)

--arrayAsTex :: forall sh e. (Shape sh, Elt e) => Array sh e -> Name -> ([C.Definition], C.Param)
--arrayAsTex _ grp =
--  let (sh, arrs)        = namesOfArray grp (undefined :: e)
--      dim               = expDim (undefined :: Exp aenv sh)
--      sh'               = [cparam| const typename $id:("DIM" ++ show dim) $id:sh |]
--      arrs'             = zipWith (\t a -> [cedecl| static $ty:t $id:a; |]) (eltTypeTex (undefined :: e)) arrs
--  in
--  (arrs', sh')

--arrayAsArg :: forall sh e. (Shape sh, Elt e) => Array sh e -> Name -> [C.Param]
--arrayAsArg _ grp =
--  let (sh, arrs)        = namesOfArray grp (undefined :: e)
--      dim               = expDim (undefined :: Exp aenv sh)
--      sh'               = [cparam| const typename $id:("DIM" ++ show dim) $id:sh |]
--      arrs'             = zipWith (\t n -> [cparam| const $ty:t * __restrict__ $id:n |]) (eltType (undefined :: e)) arrs
--  in
--  sh' : arrs'
-------------------------------------------------------------------------------------------------------------------------


-- Environments
-- ------------

aenvToCargs :: Env aenv -> [C.Param]
aenvToCargs EmptyEnv              = []
aenvToCargs (aenv `PushEnv` bnds) = aenvToCargs aenv ++ [ [cparam| $ty:t $id:name |] | (t, name) <- bnds]


-- Shapes
-- ------

-- Determine the dimensionality of an array.
--
arrDim :: forall sh e. (Shape sh, Elt e) => Array sh e -> Int
arrDim _dummy = dim (undefined::sh)

accDim :: forall sh e aenv. (Shape sh, Elt e) => OpenAcc aenv (Array sh e) -> Int
accDim _dummy = arrDim (undefined::Array sh e)
