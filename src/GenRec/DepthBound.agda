{-# OPTIONS --sized-types #-}

module GenRec.DepthBound where

open import Agda.Builtin.Size
open import Agda.Builtin.FromNat
open import Haskell.Prelude hiding (s; t)
open import Haskell.Extra.Dec
open import Haskell.Extra.Nat
open import Haskell.Extra.Refinement
open import Haskell.Law.Eq
open import Haskell.Prim.Thunk

open import GenRec.Class
open import GenRec.Inline
open import GenRec.Reflection

private variable
  i : Type
  o : @0 i → Type
  @0 s t : Size

--------------------------------------------------------------------------------

data Depth (@0 s : Size) : Type where
  Zero : Depth s
  Suc  : {@0 t : Size< s} → Depth t → Depth s

{-# COMPILE AGDA2HS Depth deriving (Eq, Ord, Show) #-}

natToDepth : Nat → Depth ∞
natToDepth n =
  ifDec (n ≟ 0) Zero λ ⦃ n≠0 ⦄ →
    case predNat n n≠0 of λ where
      (n ⟨ refl ⟩) → Suc (natToDepth n)
{-# COMPILE AGDA2HS natToDepth #-}

--------------------------------------------------------------------------------

record DepthBound (i : Type) (o : @0 i → Type) (a : Type) : Type where
  no-eta-equality
  field
    unDepthBound : Thunk (λ t → Depth t → ∀ x → Maybe (o x)) s → Depth s → Maybe a

open DepthBound public

{-# COMPILE AGDA2HS DepthBound newtype #-}

module _ (f : RecProg' (DepthBound i o) i o) where

  runDepthBound : Depth s → ∀ x → Maybe (o x)
  runDepthBound = go .force
    where
      go : Thunk (λ t → Depth t → ∀ x → Maybe (o x)) s
      go .force n x = f x .unDepthBound go n
  {-# COMPILE AGDA2HS runDepthBound #-}
  {-# FOREIGN AGDA2HS {-# INLINE runDepthBound #-} #-}

  runDepthBoundInline : Depth s → ∀ x → Maybe (o x)
  runDepthBoundInline = go .force
    where
      go : Thunk (λ t → Depth t → ∀ x → Maybe (o x)) s
      go .force n x = inline f x .unDepthBound go n
  {-# COMPILE AGDA2HS runDepthBoundInline #-}
  {-# FOREIGN AGDA2HS {-# INLINE runDepthBoundInline #-} #-}


private
  pureDB : a → DepthBound i o a
  pureDB x = record
    { unDepthBound = λ _ _ → Just x
    }
  {-# COMPILE AGDA2HS pureDB #-}

  bindDB : DepthBound i o a → (a → DepthBound i o b) → DepthBound i o b
  bindDB m k = record
    { unDepthBound = λ self n → m .unDepthBound self n >>= λ x → k x .unDepthBound self n
    }
  {-# COMPILE AGDA2HS bindDB #-}


instance
  iFunctorDepthBound     : Functor (DepthBound i o)
  iApplicativeDepthBound : Applicative (DepthBound i o)
  iMonadDepthBound       : Monad (DepthBound i o)

  iFunctorDepthBound     = record {DefaultFunctor (functorVia pureDB bindDB)}
  iApplicativeDepthBound = record {DefaultApplicative (applicativeVia pureDB bindDB)}
  iMonadDepthBound       = record {DefaultMonad (monadVia bindDB)}

  iRecurseDepthBound : Recurse i o (DepthBound i o)
  iRecurseDepthBound .recurse x = record
    { unDepthBound = λ self n → case n of λ where
        Zero    → Nothing
        (Suc n) → self .force n x
    }

  {-# COMPILE AGDA2HS iFunctorDepthBound     #-}
  {-# COMPILE AGDA2HS iApplicativeDepthBound #-}
  {-# COMPILE AGDA2HS iMonadDepthBound       #-}
  {-# COMPILE AGDA2HS iRecurseDepthBound     #-}
