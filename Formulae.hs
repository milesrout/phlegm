{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternSynonyms #-}

module Formulae where

import Data.List
import qualified Data.Set as Set
import Data.Set (Set, (\\))
import Debug.Trace
import Text.Printf

data Formula = FProp Proposition
             | FConj Formula Formula
             | FDisj Formula Formula
             | FImpl Formula Formula
             | FForall String Formula
             | FExists String Formula
             deriving (Show, Eq, Ord)

--subst x a b = trace ("\nSUBST[" ++ show x ++ " FOR " ++ show a ++ " IN " ++ show b ++ "]") $ subst x a b

class Substitutable a b where
    subst :: String -> a -> b -> b

class Render a where
    render :: a -> String

class FreeVariables a where
    freeVariables :: a -> Set String
    freeVars :: [a] -> Set String
    freeVars as = Set.unions (map freeVariables as)

instance Render a => Render [a] where
    render as = intercalate "," (map render as)

instance Substitutable Atom Formula where
    subst x a (FProp p) = FProp (subst x a p)
    subst x a (FConj l r) = FConj (subst x a l) (subst x a r)
    subst x a (FImpl l r) = FImpl (subst x a l) (subst x a r)
    subst x a (FDisj l r) = FDisj (subst x a l) (subst x a r)
    subst x a f@(FForall y b)
        | x == y    = f
        | otherwise = FForall y (subst x a b)
    subst x a f@(FExists y b)
        | x == y    = f
        | otherwise = FExists y (subst x a b)

instance FreeVariables Formula where
    freeVariables (FProp p) = freeVariables p
    freeVariables (FConj l r) = freeVars [l, r]
    freeVariables (FImpl l r) = freeVars [l, r]
    freeVariables (FDisj l r) = freeVars [l, r]
    freeVariables (FForall x a) = Set.insert x (freeVariables a)
    freeVariables (FExists x a) = Set.insert x (freeVariables a)

pattern x :∧ y = FConj x y
pattern x :∨ y = FDisj x y
pattern x :→ y = FImpl x y

x ∧ y = FConj x y
x ∨ y = FDisj x y
x → y = FImpl x y
x ∀ y = FForall x y
x ∃ y = FExists x y

instance Render Formula where
    render (FProp p) = render p
    render (FConj a b) = printf "(%s ∧ %s)" (render a) (render b)
    render (FDisj a b) = printf "(%s ∨ %s)" (render a) (render b)
    render (FImpl a b) = printf "(%s → %s)" (render a) (render b)
    render (FForall x f) = printf "∀%s.%s" x (render f)
    render (FExists x f) = printf "∃%s.%s" x (render f)

data PredSymbol = PredSymbol String Integer deriving (Eq, Ord, Show)
instance Render PredSymbol where
    render (PredSymbol name _) = name

data FuncSymbol = FuncSymbol String Integer deriving (Eq, Ord, Show)
instance Render FuncSymbol where
    render (FuncSymbol name _) = name

data Atom = AVar String | AApp FuncSymbol [Atom] deriving (Eq, Ord, Show)
instance Render Atom where
    render (AVar name) = name
    render (AApp f xs) = printf "%s(%s)" (render f) (render xs)
instance Substitutable Atom Atom where
    subst x a b@(AVar y)
        | x == y    = a
        | otherwise = b
    subst x a b@(AApp f@(FuncSymbol y n) as)
        | x == y    = b
        | otherwise = (AApp f bs)
            where bs = map (subst x a) as
instance FreeVariables Atom where
    freeVariables (AVar x) = Set.singleton x
    freeVariables (AApp (FuncSymbol p _) as) = Set.insert p (freeVars as)

data Proposition = PApp PredSymbol [Atom] deriving (Eq, Ord, Show)
instance Render Proposition where
    render (PApp p []) = render p
    render (PApp p xs) = printf "%s(%s)" (render p) (render xs)
instance Substitutable Atom Proposition where
    subst x a (PApp p as) = (PApp p bs)
        where bs = map (subst x a) as
instance FreeVariables Proposition where
    freeVariables (PApp (PredSymbol p _) as) = Set.insert p (freeVars as)

pattern Prop s = FProp (PApp (PredSymbol s 0) [])
pattern A = Prop "A"
pattern B = Prop "B"
pattern C = Prop "C"

pattern P x = FProp (PApp (PredSymbol "P" 1) [x])
pattern Q x = FProp (PApp (PredSymbol "Q" 1) [x])

x = AVar "x"
