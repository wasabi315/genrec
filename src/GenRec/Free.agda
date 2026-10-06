module GenRec.Free where

open import Haskell.Prelude
open import Haskell.Extra.Sigma
open import Haskell.Extra.Erase
open import Haskell.Law.Equality using (cong; subst)

open import GenRec.Class

{-# FOREIGN AGDA2HS
import GenRec.Class
#-}

private
  variable
    i : Type
    o : @0 i → Type

--------------------------------------------------------------------------------

data Rec (i : Type) (o : @0 i → Type) (a : Type) : Type where
  Ret  : a → Rec i o a
  Call : ∀ x → (o x → Rec i o a) → Rec i o a
{-# COMPILE AGDA2HS Rec #-}

bindRec : Rec i o a → (a → Rec i o b) → Rec i o b
bindRec (Ret a)    k = k a
bindRec (Call x j) k = Call x λ o → bindRec (j o) k
{-# COMPILE AGDA2HS bindRec #-}

instance
  iDefaultFunctorRec : DefaultFunctor (Rec i o)
  iDefaultFunctorRec .DefaultFunctor.fmap f m = bindRec m (Ret ∘ f)

  iFunctorRec : Functor (Rec i o)
  iFunctorRec = record {DefaultFunctor iDefaultFunctorRec}

  iDefaultApplicativeRec : DefaultApplicative (Rec i o)
  iDefaultApplicativeRec .DefaultApplicative.pure = Ret
  iDefaultApplicativeRec .DefaultApplicative._<*>_ mf m = bindRec mf (_<$> m)

  iApplicativeRec : Applicative (Rec i o)
  iApplicativeRec = record {DefaultApplicative iDefaultApplicativeRec}

  iDefaultMonadRec : DefaultMonad (Rec i o)
  iDefaultMonadRec .DefaultMonad._>>=_ = bindRec

  iMonadRec : Monad (Rec i o)
  iMonadRec = record {DefaultMonad iDefaultMonadRec}

  iMonadRecRec : MonadRec i o (Rec i o)
  iMonadRecRec .recurse i = Call i Ret

  {-# COMPILE AGDA2HS iFunctorRec     #-}
  {-# COMPILE AGDA2HS iApplicativeRec #-}
  {-# COMPILE AGDA2HS iMonadRec       #-}
  {-# COMPILE AGDA2HS iMonadRecRec    #-}

--------------------------------------------------------------------------------
-- Bove-Capretta method
-- The specialized accessibility predicate is constructed on the fly from a given recursive program

data Acc (prog : RecProg' (Rec i o) i o) (x : i) : Type
AccInner  : (prog : RecProg' (Rec i o) i o) (x : i) → Type
AccWorker : (prog : RecProg' (Rec i o) i o) (m : Rec i o a) → Type

-- Agda guarantees that the domain has no computational content and erases it at runtime
runRec       : ∀ prog (x : i) → @0 Acc prog x → o x
runRecWorker : ∀ prog (m : Rec i o a) → @0 AccWorker prog m → a

data Acc prog x where
  acc : AccInner prog x → Acc prog x

AccInner prog x = AccWorker prog (prog x)

AccWorker prog (Ret _)    = ⊤
AccWorker prog (Call x k) = Σ (Acc prog x) λ r₁ → AccWorker prog (k (runRec prog x r₁))

runRec prog x (acc rs) = runRecWorker prog (prog x) rs

runRecWorker prog (Ret y)    tt        = y
runRecWorker prog (Call x k) (r₁ , r₂) = runRecWorker prog (k (runRec prog x r₁)) r₂

{-# COMPILE AGDA2HS runRec       #-}
{-# COMPILE AGDA2HS runRecWorker #-}

-- variant that does not use induction-recursion
-- Rec itself can serve as a description that generates inductive graphs!

@0 ⟦_⟧ : Rec i o a → (∀ x → o x → Type) → a → Type
⟦ Ret y'   ⟧ X y = y ≡ y'
⟦ Call x k ⟧ X y = Σ[ z ∈ _ ] X x z × ⟦ k z ⟧ X y

data Graph (prog : RecProg' (Rec i o) i o) (x : i) (y : o x) : Type where
  con : ⟦ prog x ⟧ (Graph prog) y → Graph prog x y

runRecG       : ∀ prog (x : i) {@0 y : o x} → @0 Graph prog x y → Singleton y
runRecGWorker : ∀ prog {@0 y} (m : Rec i o a) → @0 ⟦ m ⟧ (Graph prog) y → Singleton y

runRecG prog x (con grf) = runRecGWorker prog (prog x) grf

runRecGWorker prog (Ret x) refl = sing x
runRecGWorker prog (Call x k) (z , (grf₁ , grf₂)) =
  case runRecG prog x grf₁ of λ where
    (sing z) → runRecGWorker prog (k z) grf₂

{-# COMPILE AGDA2HS runRecG #-}
{-# COMPILE AGDA2HS runRecGWorker #-}

--------------------------------------------------------------------------------
-- Acc is a proposition

module _ (prog : RecProg' (Rec i o) i o) where

  isPropAcc       : ∀ {x} (rs rs' : Acc prog x) → rs ≡ rs'
  isPropAccInner  : ∀ {x} (rs rs' : AccInner prog x) → rs ≡ rs'
  isPropAccWorker : (m : Rec i o a) (rs rs' : AccWorker prog m) → rs ≡ rs'

  isPropAcc (acc rs) (acc rs') = cong acc (isPropAccInner rs rs')

  isPropAccInner rs rs' = isPropAccWorker _ rs rs'

  isPropAccWorker (Ret o) tt tt = refl
  isPropAccWorker (Call i k) (r₁ , r₂) (r₁' , r₂')
    rewrite isPropAcc r₁ r₁' | isPropAccWorker _ r₂ r₂'
    = refl

  runRec-Acc-irr : ∀ i rs rs' → runRec prog i rs ≡ runRec prog i rs'
  runRec-Acc-irr i rs rs' rewrite isPropAcc rs rs' = refl
