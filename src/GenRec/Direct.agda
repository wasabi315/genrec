module GenRec.Direct where

open import Haskell.Prelude

open import GenRec.Class
open import GenRec.Inline
open import GenRec.Reflection

{-# FOREIGN AGDA2HS
import GenRec.Class
#-}

private
  variable
    i : Type
    o : @0 i → Type

--------------------------------------------------------------------------------

record Direct (i : Type) (o : @0 i → Type) (a : Type) : Type where
  no-eta-equality
  field
    unDirect : (∀ x → o x) → a

open Direct public
{-# COMPILE AGDA2HS Direct newtype #-}

module _ (f : RecProg' (Direct i o) i o) where

  {-# NON_TERMINATING #-}
  runDirect : ∀ x → o x
  runDirect = go
    where
      go : ∀ x → o x
      go x = f x .unDirect go
  {-# COMPILE AGDA2HS runDirect #-}
  {-# FOREIGN AGDA2HS {-# INLINE runDirect #-} #-}

  {-# NON_TERMINATING #-}
  runDirectInline : ∀ x → o x
  runDirectInline = go
    where
      go : ∀ x → o x
      go x = inline f x .unDirect go
  {-# COMPILE AGDA2HS runDirectInline #-}
  {-# FOREIGN AGDA2HS {-# INLINE runDirectInline #-} #-}

  runDirectOpen : (∀ x → o x) → ∀ x → o x
  runDirectOpen self x = f x .unDirect self
  {-# COMPILE AGDA2HS runDirectOpen #-}


pureDirect : a → Direct i o a
pureDirect x = record
  { unDirect = λ _ → x
  }
{-# COMPILE AGDA2HS pureDirect #-}

bindDirect : Direct i o a → (a → Direct i o b) → Direct i o b
bindDirect m k = record
  { unDirect = λ self → k (m .unDirect self) .unDirect self
  }
{-# COMPILE AGDA2HS bindDirect #-}

instance
  iFunctorDirect     : Functor (Direct i o)
  iApplicativeDirect : Applicative (Direct i o)
  iMonadDirect       : Monad (Direct i o)

  iFunctorDirect     = record {DefaultFunctor (functorVia pureDirect bindDirect)}
  iApplicativeDirect = record {DefaultApplicative (applicativeVia pureDirect bindDirect)}
  iMonadDirect       = record {DefaultMonad (monadVia bindDirect)}

  iMonadRecDirect : MonadRec i o (Direct i o)
  iMonadRecDirect .recurse x = record { unDirect = λ self → self x }

  {-# COMPILE AGDA2HS iFunctorDirect     #-}
  {-# COMPILE AGDA2HS iApplicativeDirect #-}
  {-# COMPILE AGDA2HS iMonadDirect       #-}
  {-# COMPILE AGDA2HS iMonadRecDirect     #-}
