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
  OpenAccWithName(..), OpenExpWithName, OpenFunWithName, 
  accToC
) where

  -- libraries
import Control.Monad.Trans.State
import Data.List
import qualified 
       Language.C         as C
import Language.C.Quote.C as C

  -- accelerate
import Data.Array.Accelerate.Array.Sugar
import Data.Array.Accelerate.AST                  hiding (Val(..), prj)
import Data.Array.Accelerate.Tuple

  -- friends
import Data.Array.Accelerate.C.Base
import Data.Array.Accelerate.C.Exp
import Data.Array.Accelerate.C.Type


-- Code generation monad
-- ---------------------

-- State to generate unique names and collect generated definitions.
--
data CGstate = CGstate
               { unique :: Int
               , cdefs  :: [C.Definition]   -- opposite order in which they are stored
               }

initialCGstate :: CGstate
initialCGstate = CGstate 0 []

-- State monad encapsulating the code generator state.
--
type CG = State CGstate

-- Produce a new unique name on the basis of the given base name.
--
newName :: Name -> CG Name
newName name = state $ \s@(CGstate {unique = unique}) -> (name ++ show unique, s {unique = unique + 1})

-- Store a C definition.
--
define :: C.Definition -> CG ()
define cdef = state $ \s -> ((), s {cdefs = cdef : cdefs s})


-- Generating C code from Accelerate computations
-- ----------------------------------------------

-- Name each array computation with the name of the C function that implements it.
--
data OpenAccWithName aenv t = OpenAccWithName Name (PreOpenAcc OpenAccWithName aenv t)

-- Compile an open Accelerate computation into a function definition.
--
-- The computation may contain free array variables according to the array variable environment passed as a first argument.
--
---------------------------------------------------------------------------------------------------------------------------
accToC :: forall arrs aenv. Arrays arrs => Env aenv -> OpenAcc aenv arrs -> ([C.Definition], OpenAccWithName aenv arrs)
accToC aenv acc
  = let (acc', state) = runState (accCG aenv acc) initialCGstate
    in
    (cdefs state, acc')

-- Compile an open Accelerate computation in the 'CG' monad.
--
accCG :: forall arrs aenv. Arrays arrs => Env aenv -> OpenAcc aenv arrs -> CG (OpenAccWithName aenv arrs)

accCG cFunName aenv arrs
  = define acc
  where acc = accToCDef (OpenAccWithName aenv arrs)

--accCG = error "YOU NEED TO IMPLEMENT THIS"

accToCDef :: forall arrs aenv. Arrays arrs => Env aenv -> OpenAcc aenv arrs -> C.Definition

accToCDef aenv' (OpenAcc (Alet bnd body))
  = accToCDef aenv_bnd body
  where
    (_, aenv_bnd) = aenv' `pushAccEnv` bnd

accToCDef _aenv' (OpenAcc (Use _))
  = [cedecl| int dummy_declaration; |]

accToCDef aenv' acc@(OpenAcc (Map f arr))
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

accToCDef aenv' acc@(OpenAcc (ZipWith f arr1 arr2))
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

accToCDef aenv' acc@(OpenAcc (Generate _sh f))
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

type OpenExpWithName = PreOpenExp OpenAccWithName

-- Ensure that embedded array computations are of the named variety.
--
adaptExp :: OpenExp env aenv t -> OpenExpWithName env aenv t
adaptExp e
  = case e of
      Var ix                    -> Var ix
      Let bnd body              -> Let (adaptExp bnd) (adaptExp body)
      Const c                   -> Const c
      PrimConst c               -> PrimConst c
      PrimApp f x               -> PrimApp f (adaptExp x)
      Tuple t                   -> Tuple (adaptTuple t)
      Prj ix e                  -> Prj ix (adaptExp e)
      Cond p t e                -> Cond (adaptExp p) (adaptExp t) (adaptExp e)
      Iterate n f x             -> Iterate (adaptExp n) (adaptExp f) (adaptExp x)
      IndexAny                  -> IndexAny
      IndexNil                  -> IndexNil
      IndexCons sh sz           -> IndexCons (adaptExp sh) (adaptExp sz)
      IndexHead sh              -> IndexHead (adaptExp sh)
      IndexTail sh              -> IndexTail (adaptExp sh)
      IndexSlice ix slix sh     -> IndexSlice ix (adaptExp slix) (adaptExp sh)
      IndexFull ix slix sl      -> IndexFull ix (adaptExp slix) (adaptExp sl)
      ToIndex sh ix             -> ToIndex (adaptExp sh) (adaptExp ix)
      FromIndex sh ix           -> FromIndex (adaptExp sh) (adaptExp ix)
      Intersect sh1 sh2         -> Intersect (adaptExp sh1) (adaptExp sh2)
      ShapeSize sh              -> ShapeSize (adaptExp sh)
      Shape acc                 -> Shape (adaptAcc acc)
      Index acc ix              -> Index (adaptAcc acc) (adaptExp ix)
      LinearIndex acc ix        -> LinearIndex (adaptAcc acc) (adaptExp ix)
      Foreign fo f x            -> Foreign fo (adaptFun f) (adaptExp x)
  where
    adaptTuple :: Tuple (OpenExp env aenv) t -> Tuple (OpenExpWithName env aenv) t
    adaptTuple NilTup          = NilTup
    adaptTuple (t `SnocTup` e) = adaptTuple t `SnocTup` adaptExp e
    
    -- No need to traverse embedded arrays as they must have been lifted out as part of sharing recovery.
    adaptAcc (OpenAcc (Avar ix)) = OpenAccWithName noName (Avar ix)
    adaptAcc _                   = error "D.A.A.C: unlifted array computation"

type OpenFunWithName = PreOpenFun OpenAccWithName

adaptFun :: OpenFun env aenv t -> OpenFunWithName env aenv t
adaptFun (Body e) = Body $ adaptExp e
adaptFun (Lam  f) = Lam  $ adaptFun f


---------------------------------------------------------------------------------------------------------------------------
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

-- accToC _ _ = error "D.A.A.C.Acc: unimplemented"



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
