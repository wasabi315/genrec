module GenRec.Reflection where

open import Data.List.Base as List using (List; []; _∷_; _++_)
open import Data.Nat.Base
open import Data.Product.Base
open import Data.String.Base using (String)
open import Data.Unit.Base
open import Reflection
open import Reflection.AST.Term
open import Reflection.TCM.Syntax

import Haskell.Prelude as Haskell

--------------------------------------------------------------------------------
-- Generate Functor/Applicative/Monad instances from pure and bind

private

  -- function or constructor applied to arguments
  _·_ : Name → List (Arg Term) → TC Term
  x · ts = getDefinition x >>= λ where
    (data-cons _ _) → pure (con x ts)
    _               → pure (def x ts)

  -- .meth → t
  _↦_ : Name → Term → Clause
  _↦_ meth t = clause [] (vArg (proj meth) ∷ []) t

  pattern #_ x = var x []


macro

  -- fmap f m = bind m (pure ∘ f)
  functorVia : Name → Name → Term → TC ⊤
  functorVia pure bind hole = do
    pure ← pure · []
    fmap ← prependVLams ("f" ∷ "m" ∷ []) <$>
      bind ·
        ( vArg (# 0)
        ∷ vArg (def (quote Haskell._∘_) (vArg pure ∷ vArg (# 1) ∷ []))
        ∷ [])
    unify hole (pat-lam
      ( quote Haskell.DefaultFunctor.fmap ↦ fmap
      ∷ []) [])

  -- pure     = pure
  -- mf <*> m = bind mf (λ f → f <$> m)
  applicativeVia : Name → Name → Term → TC ⊤
  applicativeVia pure bind hole = do
    pure ← pure · []
    ap   ← prependVLams ("mf" ∷ "m" ∷ []) <$>
      bind ·
        ( vArg (# 1)
        ∷ vArg (vLam "f" (def (quote Haskell._<$>_) (vArg (# 0) ∷ vArg (# 1) ∷ [])))
        ∷ [])
    unify hole (pat-lam
      ( quote Haskell.DefaultApplicative.pure  ↦ pure
      ∷ quote Haskell.DefaultApplicative._<*>_ ↦ ap
      ∷ []) [])

  -- (>>=) = bind
  monadVia : Name → Term → TC ⊤
  monadVia bind hole = do
    bind ← bind · []
    unify hole (pat-lam
      ( quote Haskell.DefaultMonad._>>=_ ↦ bind
      ∷ []) [])
