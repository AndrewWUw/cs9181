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

-- Compile an open Accelerate computation into C definitions and an open Accelerate computation, where each array
-- computation has been named. The name of an array computation may correspond to the name of the C definition
-- implementing that array computation.
--
-- The computation may contain free array variables according to the array variable environment passed as a first argument.
--
accToC :: forall arrs aenv. Arrays arrs => Env aenv -> OpenAcc aenv arrs -> ([C.Definition], OpenAccWithName aenv arrs)
accToC aenv acc
  = let (acc', state) = runState (accCG aenv acc) initialCGstate
    in
    (cdefs state, acc')

-- Compile an open Accelerate computation in the 'CG' monad.
--
accCG :: forall arrs aenv. Arrays arrs => Env aenv -> OpenAcc aenv arrs -> CG (OpenAccWithName aenv arrs)
accCG = error "YOU NEED TO IMPLEMENT THIS"

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