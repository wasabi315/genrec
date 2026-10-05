module GenRec.Class where

open import Haskell.Prelude

private variable
  i : Type
  o : @0 i → Type

--------------------------------------------------------------------------------
-- DSL for recursive programs

record MonadRec (i : Type) (o : @0 i → Type) (m : Type → Type) : Type₁ where
  field
    ⦃ super ⦄ : Monad m
    recurse   : ∀ x → m (o x)

open MonadRec ⦃ ... ⦄ public

{-# COMPILE AGDA2HS MonadRec class #-}

RecProg' : (Type → Type) → (i : Type) → (@0 i → Type) → Type
RecProg' m i o = (x : i) → m (o x)
{-# COMPILE AGDA2HS RecProg' #-}

RecProg : (i : Type) → (@0 i → Type) → Type₁
RecProg i o = ∀ {m} ⦃ _ : MonadRec i o m ⦄ → RecProg' m i o
{-# COMPILE AGDA2HS RecProg inline #-}
