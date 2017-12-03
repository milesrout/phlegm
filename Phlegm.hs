{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeSynonymInstances #-}

import Freer
import Formulae

import Control.Lens hiding (children)
import Control.Monad.RWS
import Data.Maybe
import qualified Data.Set as Set
import Data.Set (Set, (\\))
import Data.Tree
import Data.Tree.Lens
import Debug.Trace
import Text.Printf

unimplemented = error "Not yet implemented"

(%~?) :: ASetter' s a -> (a -> Maybe a) -> (s -> s)
l %~? f = l %~ (\t -> case f t of
                          Nothing -> t
                          Just s -> s)

(%=?) :: MonadState s m => ASetter' s a -> (a -> Maybe a) -> m ()
l %=? f = modify (l %~? f)

data PhlegmCommand a where
    PAssertNamed :: String -> Formula -> PhlegmCommand ()
    PAssert :: Formula -> PhlegmCommand ()
    PAssumption :: PhlegmCommand ()
    PIntro :: PhlegmCommand ()
    PElimImpl :: Formula -> PhlegmCommand ()
    PElimForall :: PhlegmCommand ()
    PSplit :: PhlegmCommand ()
    PNext :: PhlegmCommand ()
    PQed :: PhlegmCommand ()

type Phlegm = Freer PhlegmCommand 
assertNamed n f = eta (PAssertNamed n f)
assert f = eta (PAssert f)
assumption = eta PAssumption
intro = eta PIntro
elimForall = eta PElimForall
elimImpl f = eta (PElimImpl f)
split = eta PSplit
next = eta PNext
qed = eta PQed

data Goal = Goal
    { _name       :: String
    , _hypotheses :: [Formula]
    , _formula    :: Formula
    , _proved     :: Bool
    } deriving Show

data Branches a = Branches
    { _value  :: a
    , _lefts  :: [Tree a]
    , _rights :: [Tree a]
    , _base   :: Maybe (Branches a)
    } deriving (Functor, Show)

data Zipper a = Goals
    { _focus    :: a
    , _children :: [Tree a]
    , _parent   :: Maybe (Branches a)
    } deriving (Functor, Show)

type Goals = Zipper Goal

data ProverState = ProverState
    { _goals   :: Goals
    , _counter :: Int
    }

makeLenses ''Goal
makeLenses ''Branches
makeLenses ''Zipper
makeLenses ''ProverState

unicodeTick = "✓"
unicodeCross = "✗"

abbreviateGoal g = printf "%s %s: %s ⊢ %s" p n hs f
    where p = if g^.proved then unicodeTick else unicodeCross
          n = g^.name
          hs = render (g^.hypotheses)
          f = render (g^.formula)

abbreviateGoals :: Goals -> Zipper String
abbreviateGoals gs = (fmap abbreviateGoal gs) & focus %~ (++ " <--")

toTree :: Zipper a -> Tree a
toTree gs = case gs^.parent of
    Nothing -> Node (gs^.focus) (gs^.children)
    Just _  -> toTree (unsafeMoveToParent gs)

drawGoals :: Goals -> String
drawGoals = drawTree . toTree . abbreviateGoals

instance Show ProverState where
    show gs = drawGoals (gs^.goals)

moveToRight :: Zipper a -> Maybe (Zipper a)
moveToRight gs =
    case gs^.parent of
        Nothing -> Nothing
        Just bs -> case bs^.rights of
            []    -> Nothing
            (_:_) -> Just (unsafeMoveToRight gs)

disassembleFocus :: Tree a -> Branches a -> Zipper a
disassembleFocus t p = Goals { _focus = t^.root
                             , _children = t^.branches
                             , _parent = Just p }

unsafeMoveToRight :: Zipper a -> Zipper a
unsafeMoveToRight gs = disassembleFocus r p
    where (Just bs) = gs^.parent
          (r:rs) = bs^.rights
          l = reassembleFocus gs
          p = bs & lefts %~ (++[l])
                 & rights .~ rs
          --p = Branches { _value = bs^.value
          --             , _lefts = bs^.lefts ++ [l]
          --             , _rights = rs
          --             , _base = bs^.base }

reassembleFocus :: Zipper a -> Tree a
reassembleFocus gs = Node (gs^.focus) (gs^.children)

moveToParent :: Zipper a -> Maybe (Zipper a)
moveToParent gs =
    case gs^.parent of
        Nothing -> Nothing
        Just _ -> Just (unsafeMoveToParent gs)

moveToChild :: Int -> Zipper a -> Maybe (Zipper a)
moveToChild n gs = case gs^?children.ix n of
    Nothing -> Nothing
    Just child -> Just (unsafeMoveToChild gs (ls, m, rs))
        where (ls, (m:rs)) = splitAt n (gs^.children)

unsafeMoveToChild :: Zipper a -> ([Tree a], Tree a, [Tree a]) -> Zipper a
unsafeMoveToChild gs (ls,m,rs) = newGoals
    where newGoals = Goals { _focus = m^.root
                           , _children = m^.branches
                           , _parent = Just bs }
          bs = Branches { _value = gs^.focus
                        , _lefts = ls
                        , _rights = rs
                        , _base = gs^.parent }

unsafeMoveToParent :: Zipper a -> Zipper a
unsafeMoveToParent gs = Goals { _focus = nf, _children = nc, _parent = np }
    where (Just bs) = gs^.parent
          nf = bs^.value
          nc = (bs^.lefts) ++ middle ++ (bs^.rights)
          np = bs^.base
          middle = [reassembleFocus gs]

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

freshGoal, freshVar :: Prover String
freshGoal = freshName 'G'
freshVar = freshName 'x'

freshName :: Char -> Prover String
freshName k = do
    n <- counter <+= 1
    return (k:show n)

checkGoals :: Prover Bool
checkGoals = do
    oldGoals <- use goals
    when (all checkTree (oldGoals^.children)) (goals %= propagateProvedness)
    newGoals <- use goals
    return (allProved newGoals)

allProved :: Goals -> Bool
allProved = checkTree . toTree

propagateProvedness :: Goals -> Goals
propagateProvedness gs = do
    if all (^.root.proved) (gs^.children)
        then let updated = gs & focus.proved .~ True in
               case moveToParent updated of
                   Nothing -> updated
                   Just hs -> propagateProvedness hs
        else gs

checkTree :: Tree Goal -> Bool
checkTree = all (^.proved)

namedNewGoal :: String -> Formula -> [Formula] -> Goal
namedNewGoal n f hs = Goal { _name = n
                           , _formula = f
                           , _hypotheses = hs
                           , _proved = False }

newGoal :: Formula -> [Formula] -> Prover Goal
newGoal f hs = do
    name <- freshGoal
    return (namedNewGoal name f hs)

subGoal :: Goal -> Prover ()
subGoal g = do
    let node = Node g []
    goals.children %= (node:)
    goChild 0

go :: (Goals -> Maybe Goals) -> Prover ()
go f = goAlt [f, moveToParent]

goAlt :: [Goals -> Maybe Goals] -> Prover ()
goAlt [] = return ()
goAlt (f:fs) = do
    old <- use goals
    case f old of
        Nothing  -> goAlt fs
        Just new -> goals .= new

goRight :: Prover ()
goRight = go moveToRight

goChild :: Int -> Prover ()
goChild n = go (moveToChild n)

goParent :: Prover ()
goParent = go moveToParent

runPhlegm :: Phlegm a -> Prover a
runPhlegm (Pure x) = pure x
runPhlegm (Free m q) = do
    a <- traceUnPhlegm m
    runPhlegm (q a)

traceUnPhlegm :: PhlegmCommand a -> Prover a
traceUnPhlegm cmd = do
    gs <- use goals
    trace (drawGoals gs) $ unPhlegm cmd

moveToNextSubGoal :: Prover Bool
moveToNextSubGoal = do
    gs <- use goals
    case moveToRight gs of
        Just hs -> do goals .= hs
                      loopMoveToFirstChild
                      return True
        Nothing -> case moveToParent gs of
            Just hs -> do goals .= hs
                          goals.focus.proved .= True
                          moveToNextSubGoal
                          return True
            Nothing -> return False

loopMoveToFirstChild :: Prover ()
loopMoveToFirstChild = do
    gs <- use goals
    case moveToChild 0 gs of
        Just hs -> do goals .= hs
                      loopMoveToFirstChild
        Nothing -> return ()

nextSubGoal :: Prover ()
nextSubGoal = do
    moveToNextSubGoal
    return ()

unPhlegm :: PhlegmCommand a -> Prover a
unPhlegm (PAssertNamed n f) = subGoal (namedNewGoal n f [])

unPhlegm (PAssert g) = do
    f <- use (goals.focus.formula)
    hs <- use (goals.focus.hypotheses)
    newGoal f (hs ++ [g]) >>= subGoal
    goParent
    newGoal g hs >>= subGoal

unPhlegm PAssumption = do
    f <- use (goals.focus.formula)
    hs <- use (goals.focus.hypotheses)
    if elem f hs
        then do goals.focus.proved .= True
        else error "No it isn't!"
    nextSubGoal

unPhlegm PIntro = do
    f <- use (goals.focus.formula)
    case f of
        FImpl a b -> do
            hs <- use (goals.focus.hypotheses)
            newGoal b (hs ++ [a]) >>= subGoal
        FForall x a -> do
            hs <- use (goals.focus.hypotheses)
            name <- freshVar
            g <- newGoal (subst x (AVar name) a) hs
            subGoal g
        _ -> unimplemented

unPhlegm (PElimImpl x) = do
    f <- use (goals.focus.formula)
    hs <- use (goals.focus.hypotheses)
    when (not (elem x hs)) (traceShow hs $ error "That just doesn't work, mate!")
    let hs' = Set.elems (Set.delete x (Set.fromList hs))
    let f' = FImpl x f
    newGoal f' hs' >>= subGoal

unPhlegm PElimForall = do
    f <- use (goals.focus.formula)
    hs <- use (goals.focus.hypotheses)
    let foralls = filter (\x -> case x of
                                    FForall _ _ -> True
                                    _ -> False) hs
    let substs = do
        fv <- Set.elems (freeVariables f)
        (FForall x a) <- foralls
        return $ subst x (AVar fv) a
    if elem f substs
        then do goals.focus.proved .= True
        else error "That doesn't seem to be possible!"
    nextSubGoal

unPhlegm PSplit = do
    (FConj a b) <- use (goals.focus.formula)
    hs <- use (goals.focus.hypotheses)
    newGoal b hs >>= subGoal
    goParent
    newGoal a hs >>= subGoal

unPhlegm PNext = nextSubGoal

unPhlegm PQed = do
    done <- checkGoals
    gs <- use goals
    if done
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
          g = Goal { _name = "G"
                   , _formula = f
                   , _hypotheses = []
                   , _proved = False }
