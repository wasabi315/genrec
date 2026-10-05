module GenRec.Free where

open import Haskell.Prelude
open import Haskell.Extra.Sigma
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
  {-# COMPILE AGDA2HS iMonadRecRec     #-}

--------------------------------------------------------------------------------
-- Bove-Capretta method
-- The specialized accessibility predicate is constructed on the fly from a given recursive program

module _ (prog : RecProg' (Rec i o) i o) where

  data Acc (x : i) : Type
  AccInner  : (x : i) → Type
  AccWorker : ∀ {x} (m : Rec i o (o x)) → Type

  -- Agda guarantees that the domain has no computational content and erases it at runtime
  runRec       : ∀ x → @0 Acc x → o x
  runRecWorker : ∀ {@0 x} (m : Rec i o (o x)) → @0 AccWorker m → o x

  data Acc i where
    acc : AccInner i → Acc i

  AccInner i = AccWorker (prog i)

  AccWorker (Ret _)    = ⊤
  AccWorker (Call x k) = Σ (Acc x) λ r₁ → AccWorker (k (runRec x r₁))

  runRec x (acc rs) = runRecWorker (prog x) rs

  runRecWorker (Ret y)    tt        = y
  runRecWorker (Call x k) (r₁ , r₂) = runRecWorker (k (runRec x r₁)) r₂

  {-# COMPILE AGDA2HS runRec #-}
  {-# COMPILE AGDA2HS runRecWorker #-}

--------------------------------------------------------------------------------
-- Acc is a proposition
-- It follows from the fact that the domain is "collapsible" in the sense of Edwin Brady's work

module _ (prog : RecProg i o) where

  isPropAcc       : ∀ {x} (rs rs' : Acc prog x) → rs ≡ rs'
  isPropAccInner  : ∀ {x} (rs rs' : AccInner prog x) → rs ≡ rs'
  isPropAccWorker : ∀ {x} (m : Rec i o (o x)) (rs rs' : AccWorker prog m) → rs ≡ rs'

  isPropAcc (acc rs) (acc rs') = cong acc (isPropAccInner rs rs')

  isPropAccInner rs rs' = isPropAccWorker _ rs rs'

  isPropAccWorker (Ret o) tt tt = refl
  isPropAccWorker (Call i k) (r₁ , r₂) (r₁' , r₂')
    rewrite isPropAcc r₁ r₁' | isPropAccWorker _ r₂ r₂'
    = refl

  runRec-Acc-irr : ∀ i rs rs' → runRec prog i rs ≡ runRec prog i rs'
  runRec-Acc-irr i rs rs' rewrite isPropAcc rs rs' = refl
