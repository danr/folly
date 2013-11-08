module Main where

import Folly.DSL
import Folly.TPTP

import Control.Monad
import Control.Applicative

p = predicate "p"
q = predicate "q"
s = relation "s"
[a,b,c,d] = map (satsbokstav . return) "abcd"

main :: IO ()
main = zipWithM_ writeTPTP [ "test" ++ show i ++ ".p" | i <- [0 :: Integer ..] ]
    [ [ axiom'      $ forall' $ \ x y z -> s x y /\ s y z ==> s x z
      , axiom'      $ forall' $ \ x     -> neg (s x x)
      , conjecture' $ forall' $ \ x y   -> s x y ==> neg (s y x)
      ]
    , [ axiom'      $ (exists' $ \ x -> p x) ==> a
      , conjecture' $ forall' $ \ x -> p x ==> a
      ]
    , [ axiom'      $ forall' ((==>) <$> p <*> q)
      , conjecture' $ forall' p ==> forall' q
      ]
    , [ axiom'      $ forall' ((==>) <$> p <*> (neg . q))
      , conjecture' $ neg $ exists' ((/\) <$> p <*> q)
      ]
    , [ axiom'      $ forall' ((==>) <$> p <*> (neg . q))
      , conjecture' $ neg $ exists' ((/\) <$> p <*> q)
      ]
    , [ axiom'      $ (a /\ b /\ c) \/ d
      , conjecture' $ (a \/ d) /\ (b \/ d) /\ (c \/ d)
      ]
    ]

