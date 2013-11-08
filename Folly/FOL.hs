module Folly.FOL where

data Term = Fun String [Term]
          | Var String
  deriving (Eq,Ord,Show)

data EqOp = (:==) | (:!=)
  deriving (Eq,Ord,Show)

data BinOp = (:&) | (:|) | (:=>) | (:<=>)
  deriving (Eq,Ord,Show)

data Formula = EqOp Term EqOp Term
             | Rel String [Term]
             | Neg Formula
             | BinOp Formula BinOp Formula
             | Quant Quant [String] Formula
  deriving (Eq,Ord,Show)

data Quant = Forall | Exists
  deriving (Eq,Ord,Show)

mkBinOp :: BinOp -> Formula -> Formula -> Formula
mkBinOp op f g = BinOp f op g

infix 4 ===
infix 4 !=
infixr 3 &
infixr 3 /\
infixr 2 \/
infixl 1 ==>
infix  1 <=>

(==>),(&),(/\),(\/),(<=>) :: Formula -> Formula -> Formula
(==>) = mkBinOp (:=>)
(&)   = mkBinOp (:&)
(/\)  = mkBinOp (:&)
(\/)  = mkBinOp (:|)
(<=>) = mkBinOp (:<=>)

(===),(!=) :: Term -> Term -> Formula
(===) = \f g -> EqOp f (:==) g
(!=)  = \f g -> EqOp f (:!=) g

data DeclType
    = Axiom
    | Conjecture
    | Question
    | NegConj
    | Lemma
    | Hypothesis
    | Definition
  deriving (Eq,Ord,Show)

data Decl = Decl DeclType String Formula
  deriving (Eq,Ord,Show)

forall' :: [String] -> Formula -> Formula
forall' [] phi = phi
forall' xs phi = Quant Forall xs phi

exists' :: [String] -> Formula -> Formula
exists' [] phi = phi
exists' xs phi = Quant Exists xs phi
