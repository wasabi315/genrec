{-# OPTIONS --sized-types #-}

module GenRec.Fueled where

open import Agda.Builtin.Size
open import Haskell.Prelude hiding (s; t)
open import Haskell.Extra.Dec
open import Haskell.Extra.Nat
open import Haskell.Extra.Refinement
open import Haskell.Law.Eq
open import Haskell.Prim.Thunk

open import GenRec.Class
open import GenRec.Inline

{-# FOREIGN AGDA2HS
import GenRec.Class
#-}

private variable
  i : Type
  o : @0 i → Type
  @0 s t : Size

--------------------------------------------------------------------------------

data Fuel (@0 s : Size) : Type where
  Zero : Fuel s
  Suc  : {@0 t : Size< s} → Fuel t → Fuel s

{-# COMPILE AGDA2HS Fuel deriving (Eq, Ord, Show) #-}

natToFuel : Nat → Fuel ∞
natToFuel n =
  ifDec (n ≟ 0) Zero λ ⦃ n≠0 ⦄ →
    case predNat n n≠0 of λ where
      (n ⟨ refl ⟩) → Suc (natToFuel n)
{-# COMPILE AGDA2HS natToFuel #-}

--------------------------------------------------------------------------------

record Fueled (i : Type) (o : @0 i → Type) (a : Type) : Type where
  no-eta-equality
  field
    unFueled : Thunk (λ t → Fuel t → ∀ x → Maybe (o x)) s → Fuel s → Maybe a

open Fueled public

{-# COMPILE AGDA2HS Fueled newtype #-}

module _ {i : Type} {o : @0 i → Type} where

  runFueled : RecProg' (Fueled i o) i o → Fuel s → ∀ x → Maybe (o x)
  runFueled f = go .force
    where
      go : Thunk (λ t → Fuel t → ∀ x → Maybe (o x)) s
      go .force n x = f x .unFueled go n
  {-# COMPILE AGDA2HS runFueled #-}
  {-# FOREIGN AGDA2HS {-# INLINE runFueled #-} #-}

  runFueledInline : RecProg' (Fueled i o) i o → Fuel s → ∀ x → Maybe (o x)
  runFueledInline f = go .force
    where
      go : Thunk (λ t → Fuel t → ∀ x → Maybe (o x)) s
      go .force n x = inline f x .unFueled go n
  {-# COMPILE AGDA2HS runFueledInline #-}
  {-# FOREIGN AGDA2HS {-# INLINE runFueledInline #-} #-}


instance
  iDefaultFunctorFueled : DefaultFunctor (Fueled i o)
  iDefaultFunctorFueled .DefaultFunctor.fmap f m = record
    { unFueled = λ self n → f <$> m .unFueled self n
    }

  iFunctorFueled : Functor (Fueled i o)
  iFunctorFueled = record {DefaultFunctor iDefaultFunctorFueled}

  iDefaultApplicativeFueled : DefaultApplicative (Fueled i o)
  iDefaultApplicativeFueled .DefaultApplicative.pure a = record
    { unFueled = λ _ _ → Just a
    }
  iDefaultApplicativeFueled .DefaultApplicative._<*>_ mf m = record
    { unFueled = λ self n → mf .unFueled self n <*> m .unFueled self n
    }

  iApplicativeFueled : Applicative (Fueled i o)
  iApplicativeFueled = record {DefaultApplicative iDefaultApplicativeFueled}

  iDefaultMonadFueled : DefaultMonad (Fueled i o)
  iDefaultMonadFueled .DefaultMonad._>>=_ m k = record
    { unFueled = λ self n → m .unFueled self n >>= λ x → k x .unFueled self n
    }

  iMonadFueled : Monad (Fueled i o)
  iMonadFueled = record {DefaultMonad iDefaultMonadFueled}

  iMonadRecFueled : MonadRec i o (Fueled i o)
  iMonadRecFueled .recurse x = record
    { unFueled = λ self n → case n of λ where
        Zero    → Nothing
        (Suc n) → self .force n x
    }

  {-# COMPILE AGDA2HS iFunctorFueled     #-}
  {-# COMPILE AGDA2HS iApplicativeFueled #-}
  {-# COMPILE AGDA2HS iMonadFueled       #-}
  {-# COMPILE AGDA2HS iMonadRecFueled #-}
