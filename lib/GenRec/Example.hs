module GenRec.Example
  (fib, quicksortDepthBound, quicksort, Expr(..), normaliseDepthBound, normalise)
where

import qualified Data.List (partition)
import GenRec.Class (MonadRec, RecProg', Recurse(recurse))
import GenRec.DepthBound (natToDepth, runDepthBoundInline)
import GenRec.Total (runTotalInline)
import Numeric.Natural (Natural)

fib' :: MonadRec Natural Natural m => RecProg' m Natural Natural
fib' n
  = if n == 0 then pure 0 else
      if pred n == 0 then pure 1 else
        do r <- recurse (succ (pred (pred n)))
           s <- recurse (pred (pred n))
           pure (r + s)

{-# INLINE fib' #-}

fib :: Natural -> Natural
fib n = runTotalInline fib' n

quicksort' :: (Ord a, MonadRec [a] [a] m) => RecProg' m [a] [a]
quicksort' [] = pure []
quicksort' (x : xs)
  = case Data.List.partition (<= x) xs of
        (small, big) -> do small' <- recurse small
                           big' <- recurse big
                           pure $ small' ++ (x : big')

{-# INLINE quicksort' #-}

quicksortDepthBound :: Ord a => [a] -> Maybe [a]
quicksortDepthBound xs
  = runDepthBoundInline quicksort' (natToDepth 100) xs

quicksort :: Ord a => [a] -> [a]
quicksort xs = runTotalInline quicksort' xs

data Expr = Atom String
          | If Expr Expr Expr
              deriving (Show)

norm :: MonadRec Expr Expr m => RecProg' m Expr Expr
norm (Atom s) = pure (Atom s)
norm (If (Atom s) th el)
  = do th' <- recurse th
       el' <- recurse el
       pure (If (Atom s) th' el')
norm (If (If co th' el') th el)
  = do e₁ <- recurse (If th' th el)
       e₂ <- recurse (If el' th el)
       recurse (If co e₁ e₂)

{-# INLINE norm #-}

normaliseDepthBound :: Expr -> Maybe Expr
normaliseDepthBound e = runDepthBoundInline norm (natToDepth 100) e

normalise :: Expr -> Expr
normalise e = runTotalInline norm e

