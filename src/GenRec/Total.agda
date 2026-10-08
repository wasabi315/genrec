{-# OPTIONS --sized-types #-}

module GenRec.Total where

open import Agda.Builtin.Size
open import Haskell.Prelude hiding (s; t)
open import Haskell.Extra.Sigma
open import Haskell.Extra.Erase
open import Haskell.Extra.Refinement
open import Haskell.Law.Equality using (subst)
open import Haskell.Prim.Thunk

open import GenRec.Class
open import GenRec.Inline
open import GenRec.Free
open import GenRec.Reflection

{-# FOREIGN AGDA2HS
import GenRec.Class
#-}

private
  variable
    i : Type
    o : @0 i → Type
    @0 s t : Size

--------------------------------------------------------------------------------

module GraphOf (@0 recCode : RecProg' (Rec i o) i o) where

  @0 Graph : (x : i) (y : o x) (s : Size) → Type
  data @0 Graph' (code : Rec i o a) (y : a) (s : Size) : Type
  @0 GraphWorker : (code : Rec i o a) (y : a) (s : Size) → Type

  Graph x y = Graph' (recCode x) y

  data Graph' code y s where
    con : {@0 t : Size< s} → GraphWorker code y t → Graph' code y s

  GraphWorker (Ret y')   y s = y ≡ y'
  GraphWorker (Call x k) y s = Σ[ z ∈ _ ] Graph x z s × GraphWorker (k z) y s

  -- given a evaluation graph described by 'code', realise the result computationally
  Eval : @0 Rec i o a → @0 Size → Type
  Eval code s = ∀ {@0 y} → @0 Graph' code y s → Singleton y
  {-# COMPILE AGDA2HS Eval inline #-}


module @0 _ {recCode : RecProg' (Rec i o) i o} where
  open GraphOf recCode

  -- invert Graph

  invertRet : {x y : a}
    → Graph' (Ret x) y s
    → y ≡ x
  invertRet (con eq) = eq

  invertBind' : (code₁ : Rec i o a) (code₂ : a → Rec i o b) (y : b)
    → GraphWorker (code₁ >>= code₂) y s
    → Σ[ x ∈ a ] GraphWorker code₁ x s × GraphWorker (code₂ x) y s
  invertBind' (Ret x) _ z grf = x , (refl , grf)
  invertBind' (Call x code₁) code₂ y (z , (grf₁ , grf₂)) =
    let _ , (grf₃ , grf₄) = invertBind' (code₁ z) code₂ y grf₂ in
    _ , ((_ , (grf₁ , grf₃)) , grf₄)

  invertBind : (code₁ : Rec i o a) (code₂ : a → Rec i o b) {y : b}
    → Graph' (code₁ >>= code₂) y s
    → Σ[ x ∈ a ] Graph' code₁ x s × Graph' (code₂ x) y s
  invertBind code₁ code₂ {y} (con grf) =
    let _ , (grf₁ , grf₂) = invertBind' code₁ code₂ y grf in
    _ , (con grf₁ , con grf₂)

  -- Convert Acc to Graph

  Acc→Graph : ∀ {x} (rs : Acc recCode x)
    → Graph x (runRec recCode x rs) ∞

  Acc→Graph' : (code : Rec i o a) (rs : AccWorker recCode code)
    → GraphWorker code (runRecWorker recCode code rs) ∞

  Acc→Graph {x = x} (acc rs) = con (Acc→Graph' (recCode x) rs)

  Acc→Graph' (Ret y) tt = refl
  Acc→Graph' (Call x k) (r₁ , r₂) =
    let ih₁ = Acc→Graph r₁
        ih₂ = Acc→Graph' (k (runRec recCode x r₁)) r₂
    in _ , (ih₁ , ih₂)

--------------------------------------------------------------------------------

record Total (i : Type) (o : @0 i → Type) (a : Type) : Type where
  no-eta-equality
  field
    @0 code : Rec i o a
    unTotal :
      -- this gets knot-tied with the code of the recursive program being interpreted
      {@0 recCode : RecProg' (Rec i o) i o} (let open GraphOf recCode)
      -- given a function that realises the result of 'recCode x'
      → Thunk (λ t → ∀ x → Eval (recCode x) t) s
      -- realise the result of 'code'
      → Eval code s

open Total public

{-# COMPILE AGDA2HS Total newtype #-}

module _ (prog : RecProg' (Total i o) i o) where

  private
    @0 recCode : RecProg' (Rec i o) i o
    recCode x = prog x .code

  open GraphOf recCode

  runTotal : ∀ x → @0 Acc recCode x → o x
  runTotal = λ x rs → go .force x (Acc→Graph rs) .value
    where
      go : Thunk (λ t → ∀ x → Eval (recCode x) t) s
      go .force x r = prog x .unTotal {recCode = recCode} go r
  {-# COMPILE AGDA2HS runTotal #-}
  {-# FOREIGN AGDA2HS {-# INLINE runTotal #-} #-}

  runTotalInline : ∀ x → @0 Acc recCode x → o x
  runTotalInline = λ x rs → go .force x (Acc→Graph rs) .value
    where
      go : Thunk (λ t → ∀ x → Eval (recCode x) t) s
      go .force x r = inline prog x .unTotal {recCode = recCode} go r
  {-# COMPILE AGDA2HS runTotalInline #-}
  {-# FOREIGN AGDA2HS {-# INLINE runTotalInline #-} #-}


pureTotal : a → Total i o a
pureTotal x = record
  { code = Ret x
  ; unTotal = λ _ grf → x ⟨ invertRet grf ⟩
  }
{-# COMPILE AGDA2HS pureTotal #-}

bindTotal : Total i o a → (a → Total i o b) → Total i o b
bindTotal m k = record
  { code = m .code >>= λ x → k x .code
  ; unTotal = λ {s} {recCode} self {y} grf →
      let open GraphOf recCode
          @0 grfs : Σ[ x ∈ _ ] Graph' (m .code) x s × Graph' (k x .code) y s
          grfs = invertBind (m .code) (λ x → k x .code) grf
          x ⟨ eq ⟩ = m .unTotal self (grfs .snd .fst)
      in k x .unTotal self (subst (λ z → Graph' (k z .code) _ s) eq (grfs .snd .snd))
  }
{-# COMPILE AGDA2HS bindTotal #-}

instance
  iFunctorTotal : Functor (Total i o)
  iApplicativeTotal : Applicative (Total i o)
  iMonadTotal : Monad (Total i o)

  iFunctorTotal     = record {DefaultFunctor (functorVia pureTotal bindTotal)}
  iApplicativeTotal = record {DefaultApplicative (applicativeVia pureTotal bindTotal)}
  iMonadTotal       = record {DefaultMonad (monadVia bindTotal)}

  iMonadRecTotal : MonadRec i o (Total i o)
  iMonadRecTotal .recurse x = record
    { code = Call x Ret
    ; unTotal = λ where self (GraphOf.con (_ , (grf , refl))) → self .force x grf
    }

  {-# COMPILE AGDA2HS iFunctorTotal     #-}
  {-# COMPILE AGDA2HS iApplicativeTotal #-}
  {-# COMPILE AGDA2HS iMonadTotal       #-}
  {-# COMPILE AGDA2HS iMonadRecTotal    #-}
