module GenRec.Class where

open import Haskell.Prelude

{-# FOREIGN AGDA2HS {-# LANGUAGE UndecidableInstances #-} #-}

private variable
  i : Type
  o : @0 i → Type

--------------------------------------------------------------------------------
-- DSL for recursive programs

record Recurse (i : Type) (o : @0 i → Type) (m : Type → Type) : Type₁ where
  field
    recurse : ∀ x → m (o x)

open Recurse ⦃ ... ⦄ public

{-# COMPILE AGDA2HS Recurse class #-}

record ApplicativeRec (i : Type) (o : @0 i → Type) (m : Type → Type) : Type₁ where
  field
    overlap ⦃ super₁ ⦄ : Applicative m
    overlap ⦃ super₂ ⦄ : Recurse i o m

open ApplicativeRec ⦃ ... ⦄ public

{-# COMPILE AGDA2HS ApplicativeRec class #-}

record MonadRec (i : Type) (o : @0 i → Type) (m : Type → Type) : Type₁ where
  field
    overlap ⦃ super₁ ⦄ : Monad m
    overlap ⦃ super₂ ⦄ : Recurse i o m

open MonadRec ⦃ ... ⦄ public

{-# COMPILE AGDA2HS MonadRec class #-}

instance
  iApplicativeRec : ⦃ _ : Applicative m ⦄ ⦃ _ : Recurse i o m ⦄ → ApplicativeRec i o m
  iApplicativeRec = record {}
  {-# COMPILE AGDA2HS iApplicativeRec #-}

  iMonadRec : ⦃ _ : Monad m ⦄ ⦃ _ : Recurse i o m ⦄ → MonadRec i o m
  iMonadRec = record {}
  {-# COMPILE AGDA2HS iMonadRec #-}


RecProg' : (Type → Type) → (i : Type) → (@0 i → Type) → Type
RecProg' m i o = (x : i) → m (o x)
{-# COMPILE AGDA2HS RecProg' #-}

RecProg : (i : Type) → (@0 i → Type) → Type₁
RecProg i o = ∀ {m} ⦃ _ : MonadRec i o m ⦄ → RecProg' m i o
{-# COMPILE AGDA2HS RecProg inline #-}
