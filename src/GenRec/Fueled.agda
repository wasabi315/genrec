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
open import GenRec.Reflection

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

module _ (f : RecProg' (Fueled i o) i o) where

  runFueled : Fuel s → ∀ x → Maybe (o x)
  runFueled = go .force
    where
      go : Thunk (λ t → Fuel t → ∀ x → Maybe (o x)) s
      go .force n x = f x .unFueled go n
  {-# COMPILE AGDA2HS runFueled #-}
  {-# FOREIGN AGDA2HS {-# INLINE runFueled #-} #-}

  runFueledInline : Fuel s → ∀ x → Maybe (o x)
  runFueledInline = go .force
    where
      go : Thunk (λ t → Fuel t → ∀ x → Maybe (o x)) s
      go .force n x = inline f x .unFueled go n
  {-# COMPILE AGDA2HS runFueledInline #-}
  {-# FOREIGN AGDA2HS {-# INLINE runFueledInline #-} #-}


pureFueled : a → Fueled i o a
pureFueled x = record
  { unFueled = λ _ _ → Just x
  }
{-# COMPILE AGDA2HS pureFueled #-}

bindFueled : Fueled i o a → (a → Fueled i o b) → Fueled i o b
bindFueled m k = record
  { unFueled = λ self n → m .unFueled self n >>= λ x → k x .unFueled self n
  }
{-# COMPILE AGDA2HS bindFueled #-}

instance
  iFunctorFueled     : Functor (Fueled i o)
  iApplicativeFueled : Applicative (Fueled i o)
  iMonadFueled       : Monad (Fueled i o)

  iFunctorFueled     = record {DefaultFunctor (functorVia pureFueled bindFueled)}
  iApplicativeFueled = record {DefaultApplicative (applicativeVia pureFueled bindFueled)}
  iMonadFueled       = record {DefaultMonad (monadVia bindFueled)}

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
