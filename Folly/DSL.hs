{-# LANGUAGE FlexibleInstances, GeneralizedNewtypeDeriving, TypeSynonymInstances #-}
module Folly.DSL
    ( module Folly.FOL
    , module Folly.DSL
    ) where

import Control.Monad
import Control.Monad.State
import Control.Applicative hiding (empty)

import Folly.FOL hiding
    ((===),(!=),(&),(/\),(\/),(==>),(<=>),mkBinOp,forall',exists')

newtype Folly a = Folly { runFolly :: State [String] a }
  deriving (Monad,MonadState [String],Functor,Applicative)

run :: Folly a -> a
run m = evalState (runFolly m) vars
  where vars = ((`replicateM` "XYZABCUVW") =<< [1..])

newVar :: Folly String
newVar = do
    v:vs <- get
    put vs
    return v

constant :: String -> Folly Term
constant n = return (Fun n [])

unary :: String -> Folly Term -> Folly Term
unary n = liftM (Fun n . pure)

binary :: String -> Folly Term -> Folly Term -> Folly Term
binary n = liftM2 (\x y -> Fun n [x,y])

trinary :: String -> Folly Term -> Folly Term -> Folly Term -> Folly Term
trinary n = liftM3 (\x y z -> Fun n [x,y,z])

satsbokstav:: String -> Folly Formula
satsbokstav n = return (Rel n [])

predicate :: String -> Folly Term -> Folly Formula
predicate n = liftM (Rel n . pure)

relation :: String -> Folly Term -> Folly Term -> Folly Formula
relation n = liftM2 (\x y -> Rel n [x,y])

trinaryRel :: String -> Folly Term -> Folly Term -> Folly Term -> Folly Formula
trinaryRel n = liftM3 (\x y z -> Rel n [x,y,z])

mkBinOp :: BinOp -> Folly Formula -> Folly Formula -> Folly Formula
mkBinOp op = liftM2 (\f g -> BinOp f op g)

infix  4 ===
infix  4 !=
infixr 3 &
infixr 3 /\
infixr 2 \/
infixr 1 ==>
infix  1 <=>

(==>), (&), (/\), (\/), (<=>) :: Folly Formula -> Folly Formula -> Folly Formula
(==>) = mkBinOp (:=>)
(&)   = mkBinOp (:&)
(/\)  = mkBinOp (:&)
(\/)  = mkBinOp (:|)
(<=>) = mkBinOp (:<=>)

(===),(!=) :: Folly Term -> Folly Term -> Folly Formula
(===) = liftM2 (\ f g -> EqOp f (:==) g)
(!=)  = liftM2 (\ f g -> EqOp f (:!=) g)

neg :: Folly Formula -> Folly Formula
neg = fmap Neg

axiom,conjecture,question,lemma,hypothesis,definition :: String -> Folly Formula -> Decl
[axiom,conjecture,question,lemma,hypothesis,definition] =
    map (\ t s f -> Decl t s (run f))
       [ Axiom, Conjecture, Question, Lemma, Hypothesis, Definition ]

axiom',conjecture',question',lemma',hypothesis',definition' :: Folly Formula -> Decl
[axiom',conjecture',question',lemma',hypothesis',definition']
    = map ($ "x") [axiom,conjecture,question,lemma,hypothesis,definition]

class Quantifier t where
    quantifier
        :: Quant           -- ^ quantifier, Forall or Exists
        -> [String]        -- ^ accumulated used variables
        -> t               -- ^ Formula or (Term -> t)
        -> Folly Formula   -- ^ resulting formula

instance Quantifier (Folly Formula) where
    quantifier q acc f = Quant q (reverse acc) <$> f

instance Quantifier r => Quantifier (Folly Term -> r) where
    quantifier q acc f = do
        v <- newVar
        quantifier q (v:acc) (f (return (Var v)))

forall' :: Quantifier t => t -> Folly Formula
forall' = quantifier Forall []

exists' :: Quantifier t => t -> Folly Formula
exists' = quantifier Exists []

-- * Combinators

commutativeOver (~~) (#) x y = (x # y) ~~ (y # x)
commutative = commutativeOver (===)

associativeOver (~~) (#) x y z = (x # (y # z)) ~~ ((x # y) # z)
associative = associativeOver (===)

identityOver (~~) (#) c x = (x # c) ~~ x /\ (c # x) ~~ x
identity = identityOver (===)

isZeroOver (~~) (#) c x = (x # c) ~~ c /\ (c # x) ~~ c
isZero = isZeroOver (===)

distributesOver (~~) (*) (+) x y z = (x * (y + z)) ~~ ((x * y) + (x * z))
distributes = distributesOver (===)

