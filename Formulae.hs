{-# LANGUAGE GADTs #-}
{-# LANGUAGE PatternSynonyms #-}

module Formulae where

import Text.Printf

data Formula = FProp Proposition
             | FConj Formula Formula
             | FDisj Formula Formula
             | FImpl Formula Formula
             | FForall String Formula
             | FExists String Formula
             deriving Eq

pattern x :∧ y = FConj x y
pattern x :∨ y = FDisj x y
pattern x :→ y = FImpl x y

x ∧ y = FConj x y
x ∨ y = FDisj x y
x → y = FImpl x y
x ∀ y = FForall x y
x ∃ y = FExists x y

instance Show Formula where
    show (FProp p) = show p
    show (FConj a b) = printf "(%s ∧ %s)" (show a) (show b)
    show (FDisj a b) = printf "(%s ∨ %s)" (show a) (show b)
    show (FImpl a b) = printf "(%s → %s)" (show a) (show b)
    show (FForall x f) = printf "∀%s.%s" x (show f)
    show (FExists x f) = printf "∃%s.%s" x (show f)

data PredSymbol = PredSymbol String Integer deriving Eq
instance Show PredSymbol where
    show (PredSymbol name _) = name

data FuncSymbol = FuncSymbol String Integer deriving Eq
instance Show FuncSymbol where
    show (FuncSymbol name _) = name

data Atom = AVar String | AApp FuncSymbol [Atom] deriving Eq
instance Show Atom where
    show (AVar name) = name
    show (AApp f xs) = printf "%s(%s)" (show f) (show xs)

data Proposition = PApp PredSymbol [Atom] deriving Eq
instance Show Proposition where
    show (PApp p []) = show p
    show (PApp p xs) = printf "%s(%s)" (show p) (show xs)

pattern Prop s = FProp (PApp (PredSymbol s 0) [])
pattern A = Prop "A"
pattern B = Prop "B"
pattern C = Prop "C"
