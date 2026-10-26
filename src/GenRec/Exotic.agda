module GenRec.Exotic where

open import Haskell.Prelude

open import GenRec.Class
open import GenRec.Inline
open import GenRec.Reflection

private
  variable
    i : Type
    o : @0 i → Type

--------------------------------------------------------------------------------

data FunList (i : Type) (o : @0 i → Type) (a : Type) : Type where
  Done : a → FunList i o a
  More : (x : i) → FunList i o (o x → a) → FunList i o a
{-# COMPILE AGDA2HS FunList #-}

private
  fmapFL : (a → b) → FunList i o a → FunList i o b
  fmapFL f (Done x)    = Done (f x)
  fmapFL f (More x xs) = More x (fmapFL (f ∘_) xs)
  {-# COMPILE AGDA2HS fmapFL #-}

  liftA2FL : (a → b → c) → FunList i o a → FunList i o b → FunList i o c
  liftA2FL f (Done x)    ys = fmapFL (f x) ys
  liftA2FL f (More x xs) ys = More x (liftA2FL (λ g z w → f (g w) z) xs ys)
  {-# COMPILE AGDA2HS liftA2FL #-}


sell : ∀ x → FunList i o (o x)
sell x = More x (Done id)
{-# COMPILE AGDA2HS sell #-}

instance
  iDefaultFunctorFunList : DefaultFunctor (FunList i o)
  iDefaultFunctorFunList .DefaultFunctor.fmap = fmapFL

  iFunctorFunList : Functor (FunList i o)
  iFunctorFunList = record {DefaultFunctor iDefaultFunctorFunList}
  {-# COMPILE AGDA2HS iFunctorFunList #-}

  iDefaultApplicativeFunList : DefaultApplicative (FunList i o)
  iDefaultApplicativeFunList .DefaultApplicative.pure = Done
  iDefaultApplicativeFunList .DefaultApplicative._<*>_ = liftA2FL id

  iApplicativeFunList : Applicative (FunList i o)
  iApplicativeFunList = record {DefaultApplicative iDefaultApplicativeFunList}
  {-# COMPILE AGDA2HS iApplicativeFunList #-}

  iRecurseFunList : Recurse i o (FunList i o)
  iRecurseFunList .recurse = sell
  {-# COMPILE AGDA2HS iRecurseFunList #-}


module _ (f : RecProg' (FunList i o) i o) where

  {-# NON_TERMINATING #-}
  runFunList : ∀ x → o x
  runFunList = g
    where
      g : ∀ x → o x
      h : FunList i o a → a

      g x = h (f x)
      h (Done x)   = x
      h (More x m) = h m (g x)
  {-# COMPILE AGDA2HS runFunList #-}
