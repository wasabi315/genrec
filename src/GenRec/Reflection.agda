module GenRec.Reflection where

open import Data.List.Base as List using ([]; _∷_)
open import Data.Unit.Base
open import Reflection
open import Reflection.AST.Term

import Haskell.Prelude as Haskell

--------------------------------------------------------------------------------
-- Generate Functor/Applicative/Monad instances from pure and bind

private
  -- .meth → t
  _↦_ : Name → Term → Clause
  _↦_ meth t = clause [] (vArg (proj meth) ∷ []) t

  pattern #_ x = var x []
  pattern _[_,_] x t u = def x (vArg t ∷ vArg u ∷ [])


macro

  -- fmap f m = bind m (pure ∘ f)
  functorVia : Name → Name → Term → TC ⊤
  functorVia pure bind hole = do
    unify hole (pat-lam
      ( quote Haskell.DefaultFunctor.fmap ↦
          prependVLams ("m" ∷ "f" ∷ [])
            (bind [ # 0 , quote Haskell._∘_ [ def pure [] , # 1 ] ])
      ∷ []) [])

  -- pure     = pure
  -- mf <*> m = bind mf (λ f → f <$> m)
  applicativeVia : Name → Name → Term → TC ⊤
  applicativeVia pure bind hole = do
    unify hole (pat-lam
      ( quote Haskell.DefaultApplicative.pure ↦ def pure []
      ∷ quote Haskell.DefaultApplicative._<*>_ ↦
          prependVLams ("m" ∷ "mf" ∷ [])
            (bind [ # 1 , vLam "f" (quote Haskell._<$>_ [ # 0 , # 1 ]) ])
      ∷ []) [])

  -- (>>=) = bind
  monadVia : Name → Term → TC ⊤
  monadVia bind hole = do
    unify hole (pat-lam
      ( quote Haskell.DefaultMonad._>>=_ ↦ def bind []
      ∷ []) [])
