{-# LANGUAGE GADTs #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeSynonymInstances #-}

import Freer
import Formulae

import Control.Lens hiding (children)
import Control.Monad.RWS
import Data.Tree
import Data.Tree.Lens
import Debug.Trace

data PhlegmCommand a where
    AssertNamed :: String -> Formula -> PhlegmCommand ()
    Assert :: Formula -> PhlegmCommand ()

type Phlegm = Freer PhlegmCommand 
assertNamed n f = eta (AssertNamed n f)
assert f = eta (Assert f)

data Goal = Goal
    { _name       :: String
    , _hypotheses :: [Formula]
    , _formula    :: Formula
    } deriving Show

data Branches = Branches
    { _value :: Goal
    , _left  :: [Tree Goal]
    , _right :: [Tree Goal]
    , _base  :: Holey
    } deriving Show

--data Holey = Branch Branches | Top deriving Show
type Holey = Maybe Branches
pattern Branch bs = Just bs
pattern Top = Nothing

data Goals = Goals
    { _focus    :: Goal
    , _children :: [Tree Goal]
    , _parent   :: Holey
    } deriving Show

data ProverState = ProverState
    { _goals            :: Goals
    , _freshNameCounter :: Int
    } deriving Show

makeLenses ''Goal
makeLenses ''Branches
makeLenses ''Goals
makeLenses ''ProverState

moveToParent :: Goals -> Maybe Goals
moveToParent gs =
    case gs^.parent of
        Top -> Nothing
        Branch _ -> Just (unsafeMoveToParent gs)

moveToChild :: Int -> Goals -> Maybe Goals
moveToChild n gs = case gs^?children.ix n of
    Nothing -> Nothing
    Just child -> Just (unsafeMoveToChild gs (ls, m, rs))
        where (ls, (m:rs)) = splitAt n (gs^.children)

unsafeMoveToChild :: Goals -> ([Tree Goal], Tree Goal, [Tree Goal]) -> Goals
unsafeMoveToChild gs (ls,m,rs) = newGoals
    where newGoals = Goals { _focus = m^.root
                           , _children = m^.branches
                           , _parent = Branch bs }
          bs = Branches { _value = gs^.focus
                        , _left = ls
                        , _right = rs
                        , _base = gs^.parent }

unsafeMoveToParent :: Goals -> Goals
unsafeMoveToParent gs = Goals { _focus = nf, _children = nc, _parent = np }
    where (Branch bs) = gs^.parent
          nf = bs^.value
          nc = (bs^.left) ++ middle ++ (bs^.right)
          np = bs^.base
          middle = [Node g (gs^.children)]
          g = gs^.focus

indicatedGoal :: Lens' ProverState Goal
indicatedGoal = goals.focus

goto :: String -> Goals -> Goals
goto n gs = trace (show gs) $ trace (show $ moveToParent gs) $ g
    where g = Goals { _focus = undefined
                    , _children = undefined
                    , _parent = undefined }
          k = gs^..children.traverse.filtered ((==n) . _name . rootLabel)

data ProverReader = ProverReader
    {
    } deriving Show

data ProverWriter = ProverWriter
    {
    } deriving Show

instance Monoid ProverWriter where
    mempty = ProverWriter
    _ `mappend` _ = ProverWriter

type Prover a = RWS ProverReader ProverWriter ProverState a

freshName :: Prover String
freshName = do
    n <- freshNameCounter <+= 1
    return ('x':show n)

runPhlegm :: Phlegm a -> Prover a
runPhlegm (Pure x) = pure x
runPhlegm (Free m q) = do
    a <- unPhlegm m
    runPhlegm (q a)

unPhlegm :: PhlegmCommand a -> Prover a
unPhlegm (Assert f) = do
    name <- freshName
    unPhlegm (AssertNamed name f)
unPhlegm (AssertNamed n f) = do
    let subgoal = Goal { _name = n, _formula = f, _hypotheses = [] }
    let node = Node subgoal []
    goals.children %= (node:)
    oldGoals <- use goals
    let (Just newGoals) = moveToChild 0 oldGoals
    goals .= newGoals

runProver :: Formula -> Phlegm a -> (a, ProverState, ProverWriter)
runProver f m = runRWS (runPhlegm m) r s
    where r = ProverReader
          s = ProverState { _goals = gs
                          , _freshNameCounter = 0
                          }
          gs = Goals { _focus = g
                     , _children = []
                     , _parent = Top
                     }
          g = Goal { _name = "base"
                   , _formula = f
                   , _hypotheses = []
                   }
