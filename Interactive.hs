module Interactive where

import Phlegm
import Formulae

import Control.Lens
import Control.Monad
import Control.Monad.RWS
import Data.IORef
import Debug.Trace
import System.Exit

interactivelyProve :: Formula -> IO ()
interactivelyProve f = do
    proof <- newIORef (return ())
    forever $ do
        cmdString <- getLine
        modifyIORef' proof (>> (parseCommand cmdString))
        (_,s,_) <- fmap (runProver f) (readIORef proof)
        putStrLn (drawGoals (s^.goals))
        when (done s) (exitWith ExitSuccess)

parseCommand "assertNamed n f" = assertNamed "x" A
parseCommand "assert f"        = assert (P (AVar "x3"))
parseCommand "assumption"      = assumption
parseCommand "intro"           = intro
parseCommand "elimForall"      = elimForall
parseCommand "elimImpl f"      = elimImpl (P (AVar "x3"))
parseCommand "split"           = split
parseCommand "next"            = next
parseCommand "qed"             = qed
parseCommand _                 = return ()

done :: ProverState -> Bool
done s = s^.goals.focus.proved

main = interactivelyProve (("x" ∀ (P x → Q x)) → (("x" ∀ (P x)) → ("x" ∀ (Q x))))
