{-# OPTIONS --sized-types --rewriting #-}

module GenRec.Example where

open import Haskell.Prelude hiding (_<_; All; _,_,_) renaming (_,_ to infixr 4 _,_)
open import Haskell.Law.Equality using (cong)
open import Haskell.Extra.Sigma renaming (_,_ to infixr 4 _,_)

open import GenRec

--------------------------------------------------------------------------------
-- Example: Naive Fibonacci

module Fib where
  open import Haskell.Law.Eq
  open import Haskell.Law.Equality
  open import Haskell.Extra.Dec
  open import Haskell.Extra.Nat
  open import Haskell.Extra.Refinement
  open import Agda.Builtin.Equality.Rewrite
  open import Data.Nat.Base using (2+)

  opaque
    caseNat : Nat → a → (Nat → a) → a
    caseNat n z s = ifDec (n ≟ 0) z λ ⦃ n≠0 ⦄ → s (predNat n n≠0 .value)
    {-# COMPILE AGDA2HS caseNat inline #-}

    caseNatZero : (z : a) (s : Nat → a) → caseNat 0 z s ≡ z
    caseNatZero z s = refl
    {-# REWRITE caseNatZero #-}

    caseNatSuc : ∀ n (z : a) (s : Nat → a) → caseNat (suc n) z s ≡ s n
    caseNatSuc n z s with predNat (suc n) (isEquality (suc n) 0)
    ... | m ⟨ refl ⟩ = refl
    {-# REWRITE caseNatSuc  #-}


  fib' : RecProg Nat (λ _ → Nat)
  fib' n =
    caseNat n (pure 0) λ n →
    caseNat n (pure 1) λ n → do
      r ← recurse (suc n)
      s ← recurse n
      pure (r + s)
  {-# COMPILE AGDA2HS fib' #-}
  {-# FOREIGN AGDA2HS {-# INLINE fib' #-} #-}

  open module @0 A = Acc (λ n → fib' n .desc)

  @0 ∀FibAcc : ∀ n → Acc n
  ∀FibAcc 0      = acc tt
  ∀FibAcc 1      = acc tt
  ∀FibAcc (2+ n) = acc (∀FibAcc (suc n) , ∀FibAcc n , tt)

  fib : Nat → Nat
  fib n = runTotalInline fib' n (∀FibAcc n)
  {-# COMPILE AGDA2HS fib #-}

--------------------------------------------------------------------------------
-- Example: Quick sort

module Quicksort where
  open import Haskell.Data.List

  quicksort' : ⦃ Ord a ⦄ → RecProg (List a) λ _ → List a
  quicksort' [] = pure []
  quicksort' (x ∷ xs) = case partition (_<= x) xs of λ where
    (small , big) → do
      small' ← recurse small
      big' ← recurse big
      pure $ small' ++ x ∷ big'
  {-# COMPILE AGDA2HS quicksort' #-}
  {-# FOREIGN AGDA2HS {-# INLINE quicksort' #-} #-}

  quicksortFueled : ⦃ Ord a ⦄ → List a → Maybe (List a)
  quicksortFueled xs = runFueledInline quicksort' (natToFuel 100) xs
  {-# COMPILE AGDA2HS quicksortFueled #-}

  module @0 _ ⦃ _ : Ord a ⦄ where
    open import Data.Nat hiding (_+_; _*_)
    open import Data.Nat.Induction hiding (Acc; acc)
    open import Data.Nat.Properties
    open import Function using (_on_)
    open import Induction
    open import Induction.WellFounded hiding (Acc; acc)
    import Relation.Binary.Construct.On as On

    open Acc (λ x → quicksort' {a = a} x .desc)

    private

      _≺_ _≼_ : List a → List a → Type
      _≺_ = _<_ on lengthNat
      _≼_ = _≤_ on lengthNat

      ≺-wellFounded : WellFounded _≺_
      ≺-wellFounded = On.wellFounded lengthNat <-wellFounded

      open All ≺-wellFounded using () renaming (wfRec to ≺-rec)

      filter≼ : ∀ p xs → filter p xs ≼ xs
      filter≼ p [] = ≤-refl
      filter≼ p (x ∷ xs) with p x
      ... | True  = s≤s (filter≼ p xs)
      ... | False = ≤-trans (filter≼ p xs) (m≤n+m _ 1)

    ∀QuicksortAcc : ∀ xs → Acc xs
    ∀QuicksortAcc = ≺-rec _ Acc λ where
      [] rs → acc tt
      (x ∷ xs) rs →
        acc
          ( rs (s≤s (filter≼ (_<= x) xs))
          , rs (s≤s (filter≼ (not ∘ (_<= x)) xs))
          , tt )

  quicksort : ⦃ Ord a ⦄ → List a → List a
  quicksort xs = runTotalInline quicksort' xs (∀QuicksortAcc xs)
  {-# COMPILE AGDA2HS quicksort #-}

--------------------------------------------------------------------------------
-- Example: Paulson's normalisation function for if expressions

module Norm where

  data Expr : Type where
    Atom : String → Expr
    If : (cond then else : Expr) → Expr

  {-# COMPILE AGDA2HS Expr deriving (Show) #-}

  norm : RecProg Expr λ _ → Expr
  norm (Atom s) = pure (Atom s)
  norm (If (Atom s) th el) = do
    th' ← recurse th
    el' ← recurse el
    pure (If (Atom s) th' el')
  norm (If (If co th' el') th el) = do
    e₁ ← recurse (If th' th el)
    e₂ ← recurse (If el' th el)
    recurse (If co e₁ e₂)
  {-# COMPILE AGDA2HS norm #-}
  {-# FOREIGN AGDA2HS {-# INLINE norm #-} #-}

  normaliseFueled : Expr → Maybe Expr
  normaliseFueled e = runFueledInline norm (natToFuel 100) e
  {-# COMPILE AGDA2HS normaliseFueled #-}

  private module @0 _ where
    open import Data.Nat hiding (_+_; _*_)
    open import Data.Nat.Induction hiding (Acc; acc)
    open import Data.Nat.Properties
    open import Data.Product
    open import Function
    open import Induction
    open import Induction.WellFounded hiding (Acc; acc)
    open import Tactic.Cong
    import Relation.Binary.Construct.On as On

    open ≤-Reasoning
    open Acc (λ e → norm e .desc)

    private

      ∣_∣ : Expr → ℕ
      ∣ Atom _ ∣ = 1
      ∣ If co th el ∣ = ∣ co ∣ * (1 + ∣ th ∣ + ∣ el ∣)

      _≺_ _≼_ : Expr → Expr → Type
      _≺_ = _<_ on ∣_∣
      _≼_ = _≤_ on ∣_∣

      ≺-wellFounded : WellFounded _≺_
      ≺-wellFounded = On.wellFounded ∣_∣ <-wellFounded

      open All ≺-wellFounded using () renaming (wfRec to ≺-rec)

      0<∣_∣ : ∀ e → 0 < ∣ e ∣
      0<∣ Atom _ ∣ = 0<1+n
      0<∣ If co th el ∣ = (*-mono-< (0<∣ co ∣) 0<1+n)

      NonZero∣_∣ : ∀ e → NonZero ∣ e ∣
      NonZero∣ e ∣ = >-nonZero 0<∣ e ∣

      lemma1 : ∀ x th el → th ≺ If (Atom x) th el
      lemma1 x th el = begin
        suc ∣ th ∣                 ≤⟨ +-monoʳ-≤ 1 (m≤m+n ∣ th ∣ ∣ el ∣) ⟩
        suc (∣ th ∣ + ∣ el ∣)      ≡⟨ cong suc (+-identityʳ _) ⟨
        suc (∣ th ∣ + ∣ el ∣ + 0)  ∎

      lemma2 : ∀ x th el → el ≺ If (Atom x) th el
      lemma2 x th el = begin
        suc ∣ el ∣                 ≤⟨ +-monoʳ-≤ 1 (m≤n+m ∣ el ∣ ∣ th ∣) ⟩
        suc (∣ th ∣ + ∣ el ∣)      ≡⟨ cong suc (+-identityʳ _) ⟨
        suc (∣ th ∣ + ∣ el ∣ + 0)  ∎

      lemma3 : ∀ co th' el' th el → If th' th el ≺ If (If co th' el') th el
      lemma3 co th' el' th el =
        begin-strict
          ∣ th' ∣ * suc (∣ th ∣ + ∣ el ∣)
        <⟨ *-monoˡ-< (suc (∣ th ∣ + ∣ el ∣)) (begin
            suc ∣ th' ∣                       ≤⟨ s≤s (m≤m+n _ _) ⟩
            suc (∣ th' ∣ + ∣ el' ∣)           ≤⟨ m≤n*m _ _ ⦃ NonZero∣ co ∣ ⦄ ⟩
            ∣ co ∣ * suc (∣ th' ∣ + ∣ el' ∣)  ∎)
        ⟩
          ∣ co ∣ * suc (∣ th' ∣ + ∣ el' ∣) * suc (∣ th ∣ + ∣ el ∣)
        ∎

      lemma4 : ∀ co th' el' th el → If el' th el ≺ If (If co th' el') th el
      lemma4 co th' el' th el =
        begin-strict
          ∣ el' ∣ * suc (∣ th ∣ + ∣ el ∣)
        <⟨ *-monoˡ-< (suc (∣ th ∣ + ∣ el ∣)) (begin
            suc ∣ el' ∣                       ≤⟨ s≤s (m≤n+m _ _) ⟩
            suc (∣ th' ∣ + ∣ el' ∣)           ≤⟨ m≤n*m _ _ ⦃ NonZero∣ co ∣ ⦄ ⟩
            ∣ co ∣ * suc (∣ th' ∣ + ∣ el' ∣)  ∎)
        ⟩
          ∣ co ∣ * suc (∣ th' ∣ + ∣ el' ∣) * suc (∣ th ∣ + ∣ el ∣)
        ∎

      lemma5 : ∀ co th' el' th el th'' el''
        → th'' ≼ If th' th el
        → el'' ≼ If el' th el
        → If co th'' el'' ≺ If (If co th' el') th el
      lemma5 co th' el' th el th'' el'' h₁ h₂ =
        begin-strict
          ∣ co ∣ * suc (∣ th'' ∣ + ∣ el'' ∣)
        ≤⟨ *-monoʳ-≤ ∣ co ∣ (s≤s (+-mono-≤ h₁ h₂)) ⟩
          ∣ co ∣ * suc ⌞ ∣ th' ∣ * suc (∣ th ∣ + ∣ el ∣) + ∣ el' ∣ * suc (∣ th ∣ + ∣ el ∣) ⌟
        ≡⟨ cong! (*-distribʳ-+ _ ∣ th' ∣ ∣ el' ∣) ⟨
          ∣ co ∣ * suc ((∣ th' ∣ + ∣ el' ∣) * suc (∣ th ∣ + ∣ el ∣))
        <⟨ *-monoʳ-< _ ⦃ NonZero∣ co ∣ ⦄
            (+-monoˡ-< _ (s<s (+-mono-<-≤ 0<∣ th ∣ (<⇒≤ 0<∣ el ∣))))
        ⟩
          ∣ co ∣ * (suc (∣ th ∣ + ∣ el ∣) + (∣ th' ∣ + ∣ el' ∣) * suc (∣ th ∣ + ∣ el ∣))
        ≡⟨ *-assoc ∣ co ∣ _ _ ⟨
          ∣ co ∣ * suc (∣ th' ∣ + ∣ el' ∣) * suc (∣ th ∣ + ∣ el ∣)
        ∎

      norm≼ : ∀ e (rs : Acc e) → result e rs ≼ e
      norm≼ (Atom _) (acc _) = ≤-refl
      norm≼ (If (Atom _) th el) (acc (r₁ , r₂ , tt)) =
        s≤s (+-monoˡ-≤ _ (+-mono-≤ (norm≼ th r₁) (norm≼ el r₂)))
      norm≼ (If (If co th' el') th el) (acc (r₁ , r₂ , r₃ , tt))
        using e₁ ← result (If th' th el) r₁
        using e₂ ← result (If el' th el) r₂ =
        begin
          ∣ result (If co e₁ e₂) r₃ ∣
        ≤⟨ norm≼ (If co e₁ e₂) r₃ ⟩
          ∣ co ∣ * suc (∣ e₁ ∣ + ∣ e₂ ∣)
        ≤⟨ *-monoʳ-≤ ∣ co ∣ (s≤s (+-mono-≤ (norm≼ (If th' th el) r₁) (norm≼ (If el' th el) r₂))) ⟩
          ∣ co ∣ * suc ⌞ ∣ th' ∣ * suc (∣ th ∣ + ∣ el ∣) + (∣ el' ∣ * suc (∣ th ∣ + ∣ el ∣)) ⌟
        ≡⟨ cong! (*-distribʳ-+ _ ∣ th' ∣ ∣ el' ∣) ⟨
          ∣ co ∣ * suc ((∣ th' ∣ + ∣ el' ∣) * suc (∣ th ∣ + ∣ el ∣))
        ≤⟨ *-monoʳ-≤ ∣ co ∣ (+-monoʳ-≤ 1 (m≤n+m _ (∣ th ∣ + ∣ el ∣))) ⟩
          ∣ co ∣ * (suc (∣ th ∣ + ∣ el ∣) + (∣ th' ∣ + ∣ el' ∣) * suc (∣ th ∣ + ∣ el ∣))
        ≡⟨ *-assoc ∣ co ∣ _ _ ⟨
          ∣ co ∣ * suc (∣ th' ∣ + ∣ el' ∣) * suc (∣ th ∣ + ∣ el ∣)
        ∎

    ∀NormAcc : ∀ e → Acc e
    ∀NormAcc = ≺-rec _ Acc λ where
      (Atom _) _ → acc tt
      (If (Atom x) th el) rs →
        let r₁ = rs (lemma1 x th el)
            r₂ = rs (lemma2 x th el)
        in acc (r₁ , r₂ , tt)
      (If (If co th' el') th el) rs →
        let r₁ = rs (lemma3 co th' el' th el)
            e₁ = result (If th' th el) r₁
            r₂ = rs (lemma4 co th' el' th el)
            e₂ = result (If el' th el) r₂
            r₃ = rs (lemma5 co th' el' th el e₁ e₂ (norm≼ _ r₁) (norm≼ _ r₂))
        in acc (r₁ , r₂ , r₃ , tt)

  normalise : Expr → Expr
  normalise e = runTotalInline norm e (∀NormAcc e)
  {-# COMPILE AGDA2HS normalise #-}
