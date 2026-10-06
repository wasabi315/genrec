module GenRec.Free where

import GenRec.Class (MonadRec, RecProg')

import GenRec.Class

data Rec i o a = Ret a
               | Call i (o -> Rec i o a)

bindRec :: Rec i o a -> (a -> Rec i o b) -> Rec i o b
bindRec (Ret a) k = k a
bindRec (Call x j) k = Call x (\ o -> bindRec (j o) k)

instance Functor (Rec i o) where
    fmap f m = bindRec m (Ret . f)

instance Applicative (Rec i o) where
    pure = Ret
    mf <*> m = bindRec mf (<$> m)

instance Monad (Rec i o) where
    (>>=) = bindRec

instance MonadRec i o (Rec i o) where
    recurse i = Call i Ret

runRec :: (i -> Rec i o o) -> i -> o
runRec prog x = runRecWorker prog (prog x)

runRecWorker :: (i -> Rec i o o) -> Rec i o a -> a
runRecWorker prog (Ret y) = y
runRecWorker prog (Call x k)
  = runRecWorker prog (k (runRec prog x))

runRecG :: (i -> Rec i o o) -> i -> o
runRecG prog x = runRecGWorker prog (prog x)

runRecGWorker :: RecProg' (Rec i o) i o -> Rec i o a -> a
runRecGWorker prog (Ret x) = x
runRecGWorker prog (Call x k)
  = case runRecG prog x of
        z -> runRecGWorker prog (k z)

