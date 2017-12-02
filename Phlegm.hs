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
import Text.Printf

data PhlegmCommand a where
    PAssertNamed :: String -> Formula -> PhlegmCommand ()
    PAssert :: Formula -> PhlegmCommand ()
    PAssumption :: PhlegmCommand ()
    PIntro :: PhlegmCommand ()
    PSplit :: PhlegmCommand ()
    PQed :: PhlegmCommand ()

type Phlegm = Freer PhlegmCommand 
assertNamed n f = eta (PAssertNamed n f)
assert f = eta (PAssert f)
assumption = eta PAssumption
intro = eta PIntro
split = eta PSplit
qed = eta PQed

data Goal = Goal
    { _name       :: String
    , _hypotheses :: [Formula]
    , _formula    :: Formula
    , _proved     :: Bool
    } deriving Show

data Branches = Branches
    { _value  :: Goal
    , _lefts  :: [Tree Goal]
    , _rights :: [Tree Goal]
    , _base   :: Maybe Branches
    } deriving Show

data Goals = Goals
    { _focus    :: Goal
    , _children :: [Tree Goal]
    , _parent   :: Maybe Branches
    } deriving Show

data ProverState = ProverState
    { _goals   :: Goals
    , _counter :: Int
    }

makeLenses ''Goal
makeLenses ''Branches
makeLenses ''Goals
makeLenses ''ProverState

unicodeTick = "Y"
unicodeCross = "N"

abbreviateGoal g = printf "%s %s ⊢ %s" p hs f
    where p = if g^.proved then unicodeTick else unicodeCross
          hs = show (g^.hypotheses)
          f = show (g^.formula)

toTree :: Goals -> Tree Goal
toTree gs = case gs^.parent of
    Nothing -> Node (gs^.focus) (gs^.children)
    Just _  -> toTree (unsafeMoveToParent gs)

drawGoals :: Goals -> String
drawGoals = drawTree . (fmap abbreviateGoal) . toTree

instance Show ProverState where
    show gs = drawGoals (gs^.goals)

moveToParent :: Goals -> Maybe Goals
moveToParent gs =
    case gs^.parent of
        Nothing -> Nothing
        Just _ -> Just (unsafeMoveToParent gs)

moveToChild :: Int -> Goals -> Maybe Goals
moveToChild n gs = case gs^?children.ix n of
    Nothing -> Nothing
    Just child -> Just (unsafeMoveToChild gs (ls, m, rs))
        where (ls, (m:rs)) = splitAt n (gs^.children)

unsafeMoveToChild :: Goals -> ([Tree Goal], Tree Goal, [Tree Goal]) -> Goals
unsafeMoveToChild gs (ls,m,rs) = newGoals
    where newGoals = Goals { _focus = m^.root
                           , _children = m^.branches
                           , _parent = Just bs }
          bs = Branches { _value = gs^.focus
                        , _lefts = ls
                        , _rights = rs
                        , _base = gs^.parent }

unsafeMoveToParent :: Goals -> Goals
unsafeMoveToParent gs = Goals { _focus = nf, _children = nc, _parent = np }
    where (Just bs) = gs^.parent
          nf = bs^.value
          nc = (bs^.lefts) ++ middle ++ (bs^.rights)
          np = bs^.base
          middle = [Node g (gs^.children)]
          g = gs^.focus

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
    n <- counter <+= 1
    return ('x':show n)

runPhlegm :: Phlegm a -> Prover a
runPhlegm (Pure x) = pure x
runPhlegm (Free m q) = do
    a <- unPhlegm m
    runPhlegm (q a)

checkGoals :: Goals -> Bool
checkGoals = checkTree . toTree

checkTree :: Tree Goal -> Bool
checkTree = all (^.proved)

namedNewGoal :: String -> Formula -> [Formula] -> Goal
namedNewGoal n f hs = Goal { _name = n
                           , _formula = f
                           , _hypotheses = hs
                           , _proved = False }

newGoal :: Formula -> [Formula] -> Prover Goal
newGoal f hs = do
    name <- freshName
    return (namedNewGoal name f hs)

subGoal :: Goal -> Prover ()
subGoal g = do
    let node = Node g []
    goals.children %= (node:)
    goChild 0

goChild :: Int -> Prover ()
goChild n = do
    oldGoals <- use goals
    let (Just newGoals) = moveToChild n oldGoals
    goals .= newGoals

goParent :: Prover ()
goParent = do
    oldGoals <- use goals
    let (Just newGoals) = moveToParent oldGoals
    goals .= newGoals

unPhlegm :: PhlegmCommand a -> Prover a
unPhlegm (PAssert f)        = (newGoal f []) >>= subGoal
unPhlegm (PAssertNamed n f) = subGoal (namedNewGoal n f [])
unPhlegm PIntro = do
    (FImpl a b) <- use (goals.focus.formula)
    hs <- use (goals.focus.hypotheses)
    g <- newGoal b (hs ++ [a])
    subGoal g
unPhlegm PSplit = do
    (FConj a b) <- use (goals.focus.formula)
    hs <- use (goals.focus.hypotheses)
    gB <- newGoal b hs
    subGoal gB
    goParent
    gA <- newGoal a hs
    subGoal gA
unPhlegm PAssumption = do
    f <- use (goals.focus.formula)
    hs <- use (goals.focus.hypotheses)
    if elem f hs
        then goals.focus.proved .= True
        else error "No it isn't!"
    goParent
unPhlegm PQed = do
    gs <- use goals
    trace (drawGoals gs) $ if checkGoals gs
        then return()
        else error "Nope!"


runProver :: Formula -> Phlegm a -> (a, ProverState, ProverWriter)
runProver f m = runRWS (runPhlegm m) r s
    where r = ProverReader
          s = ProverState { _goals = gs
                          , _counter = 0 }
          gs = Goals { _focus = g
                     , _children = []
                     , _parent = Nothing }
          g = Goal { _name = "base"
                   , _formula = f
                   , _hypotheses = []
                   , _proved = False }
