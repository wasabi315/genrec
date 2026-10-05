module GenRec.Direct where

open import Haskell.Prelude

open import GenRec.Class
open import GenRec.Inline

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

module _ {i : Type} {o : @0 i → Type} where

  {-# NON_TERMINATING #-}
  runDirect : RecProg' (Direct i o) i o → ∀ x → o x
  runDirect f = go
    where
      go : ∀ x → o x
      go x = f x .unDirect go
  {-# COMPILE AGDA2HS runDirect #-}
  {-# FOREIGN AGDA2HS {-# INLINE runDirect #-} #-}

  {-# NON_TERMINATING #-}
  runDirectInline : RecProg' (Direct i o) i o → ∀ x → o x
  runDirectInline f = go
    where
      go : ∀ x → o x
      go x = inline f x .unDirect go
  {-# COMPILE AGDA2HS runDirectInline #-}
  {-# FOREIGN AGDA2HS {-# INLINE runDirectInline #-} #-}


instance
  iDefaultFunctorDirect : DefaultFunctor (Direct i o)
  iDefaultFunctorDirect .DefaultFunctor.fmap f m = record
    { unDirect = f ∘ m .unDirect
    }

  iFunctorDirect : Functor (Direct i o)
  iFunctorDirect = record {DefaultFunctor iDefaultFunctorDirect}

  iDefaultApplicativeDirect : DefaultApplicative (Direct i o)
  iDefaultApplicativeDirect .DefaultApplicative.pure a = record
    { unDirect = λ _ → a
    }
  iDefaultApplicativeDirect .DefaultApplicative._<*>_ mf m = record
    { unDirect = λ self → mf .unDirect self (m .unDirect self)
    }

  iApplicativeDirect : Applicative (Direct i o)
  iApplicativeDirect = record {DefaultApplicative iDefaultApplicativeDirect}

  iDefaultMonadDirect : DefaultMonad (Direct i o)
  iDefaultMonadDirect .DefaultMonad._>>=_ m k = record
    { unDirect = λ self → k (m .unDirect self) .unDirect self
    }

  iMonadDirect : Monad (Direct i o)
  iMonadDirect = record {DefaultMonad iDefaultMonadDirect}

  iMonadRecDirect : MonadRec i o (Direct i o)
  iMonadRecDirect .recurse x = record { unDirect = λ self → self x }

  {-# COMPILE AGDA2HS iFunctorDirect     #-}
  {-# COMPILE AGDA2HS iApplicativeDirect #-}
  {-# COMPILE AGDA2HS iMonadDirect       #-}
  {-# COMPILE AGDA2HS iMonadRecDirect     #-}
