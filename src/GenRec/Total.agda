{-# OPTIONS --sized-types #-}

module GenRec.Total where

open import Agda.Builtin.Size
open import Haskell.Prelude hiding (s; t)
open import Haskell.Extra.Sigma
open import Haskell.Extra.Erase
open import Haskell.Extra.Refinement
open import Haskell.Law.Equality using (cong; subst)
open import Haskell.Prim.Thunk

open import GenRec.Class
open import GenRec.Inline
open import GenRec.Free

{-# FOREIGN AGDA2HS
import GenRec.Class
#-}

private
  variable
    i : Type
    o : @0 i → Type
    @0 s t : Size

--------------------------------------------------------------------------------

module @0 _ (prog : RecProg' (Rec i o) i o) where

  GraphS : (s : Size) (x : i) (y : o x) → Type
  data GraphS' (s : Size) (desc : Rec i o a) (y : a) : Type

  GraphS s x y = GraphS' s (prog x) y

  data GraphS' s desc y where
    con : {@0 t : Size< s} → ⟦ desc ⟧ (GraphS t) y → GraphS' s desc y


@0 split' : {prog : RecProg' (Rec i o) i o} (m : Rec i o a) (k : a → Rec i o b) (z : b)
  → ⟦ m >>= k ⟧ (GraphS prog s) z
  → Σ[ x ∈ a ] ⟦ m ⟧ (GraphS prog s) x × ⟦ k x ⟧ (GraphS prog s) z
split' (Ret y) k z r = y , (refl , r)
split' (Call x j) k z (y , (r₁ , r₂)) =
  let w , (r₃ , r₄) = split' (j y) k z r₂ in
  w , ((y , (r₁ , r₃)) , r₄)

@0 split : {prog : RecProg' (Rec i o) i o} (m : Rec i o a) (k : a → Rec i o b) (z : b)
  → GraphS' prog s (m >>= k) z
  → Σ[ x ∈ a ] GraphS' prog s m x × GraphS' prog s (k x) z
split m k z (con r) =
  let y , (r₁ , r₂) = split' m k z r in
  y , (con r₁ , con r₂)

record Total (i : Type) (o : @0 i → Type) (a : Type) : Type where
  no-eta-equality
  field
    @0 desc : Rec i o a
    run : ∀ {@0 prog : RecProg' (Rec i o) i o}
      → Thunk (λ t → ∀ x {@0 y} → @0 GraphS prog t x y → Singleton y) s
      → ∀ {@0 y} → @0 GraphS' prog s desc y → Singleton y

open Total public

{-# COMPILE AGDA2HS Total newtype #-}

module _ (prog : RecProg' (Total i o) i o) where

  runTotal : ∀ x {@0 y} → @0 GraphS (λ x → prog x .desc) ∞ x y → Singleton y
  runTotal = go .force
    where
      go : Thunk (λ t → ∀ x {@0 y} → @0 GraphS (λ x → prog x .desc) t x y → Singleton y) s
      go .force x r = inline prog x .run {prog = λ x → prog x .desc} go r
  {-# COMPILE AGDA2HS runTotal #-}


pureTotal : a → Total i o a
pureTotal x = record
  { desc = pure x
  ; run  = λ where _ (con refl) → sing x
  }
{-# COMPILE AGDA2HS pureTotal #-}

bindTotal : Total i o a → (a → Total i o b) → Total i o b
bindTotal m k = record
  { desc = m .desc >>= λ x → k x .desc
  ; run = λ {s = s} self {y} r →
      let @0 h : _
          h = split (m .desc) (λ x → k x .desc) y r
      in case m .run self (h .snd .fst) of λ where
        (z ⟨ eq ⟩) → k z .run self (subst (λ w → GraphS' _ s (k w .desc) _) eq (h .snd .snd))
  }
{-# COMPILE AGDA2HS bindTotal #-}

recurseTotal : ∀ x → Total i o (o x)
recurseTotal x = record
  { desc = recurse x
  ; run  = λ where self (con (_ , (r , refl))) → self .force x r
  }
{-# COMPILE AGDA2HS recurseTotal #-}

instance
  iDefaultFunctorTotal : DefaultFunctor (Total i o)
  iDefaultFunctorTotal .DefaultFunctor.fmap f m = bindTotal m (pureTotal ∘ f)

  iFunctorTotal : Functor (Total i o)
  iFunctorTotal = record {DefaultFunctor iDefaultFunctorTotal}

  iDefaultApplicativeTotal : DefaultApplicative (Total i o)
  iDefaultApplicativeTotal .DefaultApplicative.pure = pureTotal
  iDefaultApplicativeTotal .DefaultApplicative._<*>_ mf m = bindTotal mf (_<$> m)

  iApplicativeTotal : Applicative (Total i o)
  iApplicativeTotal = record {DefaultApplicative iDefaultApplicativeTotal}

  iDefaultMonadTotal : DefaultMonad (Total i o)
  iDefaultMonadTotal .DefaultMonad._>>=_ = bindTotal

  iMonadTotal : Monad (Total i o)
  iMonadTotal = record {DefaultMonad iDefaultMonadTotal}

  iMonadRecTotal : MonadRec i o (Total i o)
  iMonadRecTotal .MonadRec.recurse = recurseTotal

  {-# COMPILE AGDA2HS iFunctorTotal     #-}
  {-# COMPILE AGDA2HS iApplicativeTotal #-}
  {-# COMPILE AGDA2HS iMonadTotal       #-}
  {-# COMPILE AGDA2HS iMonadRecTotal    #-}
