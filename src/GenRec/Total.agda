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

data Desc (i : Type) (o : @0 i → Type) (a : Type) : Type where
  Ret  : a → Desc i o a
  Call : ∀ x → (o x → Desc i o a) → Desc i o a

pureDesc : a → Desc i o a
pureDesc = Ret

bindDesc : Desc i o a → (a → Desc i o b) → Desc i o b
bindDesc (Ret a)    k = k a
bindDesc (Call x j) k = Call x λ o → bindDesc (j o) k

instance
  iFunctorDesc     : Functor (Desc i o)
  iApplicativeDesc : Applicative (Desc i o)
  iMonadDesc       : Monad (Desc i o)

  iFunctorDesc     = record {DefaultFunctor (functorVia pureDesc bindDesc)}
  iApplicativeDesc = record {DefaultApplicative (applicativeVia pureDesc bindDesc)}
  iMonadDesc       = record {DefaultMonad (monadVia bindDesc)}

--------------------------------------------------------------------------------

private module Graph (@0 recDesc : ∀ x → Desc i o (o x)) where

  @0 Graph : (x : i) (y : o x) (s : Size) → Type
  data @0 GraphOf (desc : Desc i o a) (y : a) (s : Size) : Type
  @0 GraphStep : (desc : Desc i o a) (y : a) (s : Size) → Type

  Graph x y = GraphOf (recDesc x) y

  data GraphOf desc y s where
    con : {t : Size< s} → GraphStep desc y t → GraphOf desc y s

  GraphStep (Ret y')   y s = y ≡ y'
  GraphStep (Call x d) y s = Σ[ z ∈ _ ] Graph x z s × GraphStep (d z) y s

  -- given a evaluation graph described by 'desc', realise the result computationally
  Eval : @0 Desc i o a → @0 Size → Type
  Eval desc s = ∀ {@0 y} → @0 GraphOf desc y s → Singleton y
  {-# COMPILE AGDA2HS Eval inline #-}


private module @0 _ {recDesc : ∀ x → Desc i o (o x)} where
  open Graph recDesc

  -- invert Graph

  invertRet : {x y : a}
    → GraphOf (Ret x) y s
    → y ≡ x
  invertRet (con eq) = eq

  invertBindStep : (d₁ : Desc i o a) (d₂ : a → Desc i o b) (y : b)
    → GraphStep (d₁ >>= d₂) y s
    → Σ[ x ∈ a ] GraphStep d₁ x s × GraphStep (d₂ x) y s
  invertBindStep (Ret x) _ z g = x , (refl , g)
  invertBindStep (Call x d₁) d₂ y (z , (g₁ , g₂)) =
    let _ , (g₃ , g₄) = invertBindStep (d₁ z) d₂ y g₂ in
    _ , ((_ , (g₁ , g₃)) , g₄)

  invertBind : (d₁ : Desc i o a) (d₂ : a → Desc i o b) {y : b}
    → GraphOf (d₁ >>= d₂) y s
    → Σ[ x ∈ a ] GraphOf d₁ x s × GraphOf (d₂ x) y s
  invertBind d₁ d₂ {y} (con g) =
    let _ , (g₁ , g₂) = invertBindStep d₁ d₂ y g in
    _ , (con g₁ , con g₂)

--------------------------------------------------------------------------------

module Acc (recDesc : ∀ x → Desc i o (o x)) where

  data Acc (x : i) : Type
  AccStep : (desc : Desc i o a) → Type

  result     : ∀ x → @0 Acc x → o x
  resultStep : (desc : Desc i o a) → @0 AccStep desc → a

  data Acc x where
    acc : AccStep (recDesc x) → Acc x

  AccStep (Ret _)    = ⊤
  AccStep (Call x d) = Σ[ rs ∈ Acc x ] AccStep (d (result x rs))

  result x (acc rs) = resultStep (recDesc x) rs

  resultStep (Ret y)    tt          = y
  resultStep (Call x d) (rs₁ , rs₂) = resultStep (d (result x rs₁)) rs₂


private module @0 _ {recDesc : ∀ x → Desc i o (o x)} where
  open Graph recDesc
  open Acc   recDesc

  -- Convert Acc to Graph

  Acc→Graph         : ∀ x (rs : Acc x) → Graph x (result x rs) ∞
  AccStep→GraphStep : (d : Desc i o a) (rs : AccStep d) → GraphStep d (resultStep d rs) ∞

  Acc→Graph x (acc rs) = con (AccStep→GraphStep (recDesc x) rs)

  AccStep→GraphStep (Ret y) tt = refl
  AccStep→GraphStep (Call x d) (rs₁ , rs₂) =
    let g₁ = Acc→Graph x rs₁
        g₂ = AccStep→GraphStep (d (result x rs₁)) rs₂
    in _ , (g₁ , g₂)

--------------------------------------------------------------------------------

record Total (i : Type) (o : @0 i → Type) (a : Type) : Type where
  no-eta-equality
  field
    @0 desc : Desc i o a
    -- implicit for better printing
    {unTotal} :
      {@0 selfDesc : ∀ x → Desc i o (o x)} (let open Graph selfDesc)
      -- given a function that realises the result of 'selfDesc x'
      → (self : Thunk (λ t → ∀ x → Eval (selfDesc x) t) s)
      -- realise the result of 'desc'
      → Eval desc s

open Total public

{-# COMPILE AGDA2HS Total newtype #-}

module _ (prog : RecProg' (Total i o) i o) where

  private
    @0 selfDesc : ∀ x → Desc i o (o x)
    selfDesc x = prog x .desc

    open module @0 G = Graph selfDesc
    open module @0 A = Acc selfDesc

  runTotal : ∀ x → @0 Acc x → o x
  runTotal = λ x rs → go .force x (Acc→Graph x rs) .value
    where
      go : Thunk (λ t → ∀ x → Eval (selfDesc x) t) s
      go .force x r = prog x .unTotal {selfDesc = selfDesc} go r
  {-# COMPILE AGDA2HS runTotal #-}
  {-# FOREIGN AGDA2HS {-# INLINE runTotal #-} #-}

  runTotalInline : ∀ x → @0 Acc x → o x
  runTotalInline = λ x rs → go .force x (Acc→Graph x rs) .value
    where
      go : Thunk (λ t → ∀ x → Eval (selfDesc x) t) s
      go .force x r = inline prog x .unTotal {selfDesc = selfDesc} go r
  {-# COMPILE AGDA2HS runTotalInline #-}
  {-# FOREIGN AGDA2HS {-# INLINE runTotalInline #-} #-}

module _ {@0 selfDesc : ∀ x → Desc i o (o x)} where opaque
  open Graph selfDesc

  pureTotal' : (x : a)
    → (self : Thunk (λ t → ∀ x → Eval (selfDesc x) t) s)
    → Eval (Ret x) s
  pureTotal' x = λ _ g → x ⟨ invertRet g ⟩
  {-# COMPILE AGDA2HS pureTotal' inline #-}

  bindTotal' : (m : Total i o a) (k : a → Total i o b)
    → (self : Thunk (λ t → ∀ x → Eval (selfDesc x) t) s)
    → Eval (m .desc >>= λ x → k x .desc) s
  bindTotal' {s = s} m k = λ self {y} g →
    let @0 gs : Σ[ x ∈ _ ] GraphOf (m .desc) x s × GraphOf (k x .desc) y s
        gs = invertBind (m .desc) (λ x → k x .desc) g
        x ⟨ eq ⟩ = m .unTotal self (gs .snd .fst)
    in k x .unTotal self (subst (λ z → GraphOf (k z .desc) _ s) eq (gs .snd .snd))
  {-# COMPILE AGDA2HS bindTotal' inline #-}

  recurseTotal' : (x : i)
    → (self : Thunk (λ t → ∀ x → Eval (selfDesc x) t) s)
    → Eval (Call x Ret) s
  recurseTotal' x = λ where self (con (_ , (g , refl))) → self .force x g
  {-# COMPILE AGDA2HS recurseTotal' inline #-}


pureTotal : a → Total i o a
pureTotal x = record
  { desc = Ret x
  ; unTotal = pureTotal' x
  }
{-# COMPILE AGDA2HS pureTotal #-}

bindTotal : Total i o a → (a → Total i o b) → Total i o b
bindTotal m k = record
  { desc = m .desc >>= λ x → k x .desc
  ; unTotal = bindTotal' m k
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
    { desc = Call x Ret
    ; unTotal = recurseTotal' x
    }

  {-# COMPILE AGDA2HS iFunctorTotal     #-}
  {-# COMPILE AGDA2HS iApplicativeTotal #-}
  {-# COMPILE AGDA2HS iMonadTotal       #-}
  {-# COMPILE AGDA2HS iMonadRecTotal    #-}
