module Main where

import Folly.DSL hiding (neg)
import qualified Folly.DSL as Folly
import Folly.TPTP

import Prelude hiding (succ,(+),pred,(*),gcd)

zero = constant "zero"
one  = constant "one"
(+)  = binary   "plus"
(*)  = binary   "mul"
neg  = unary    "neg"
gcd  = binary   "gcd"

infixl 5 +
infixl 6 *
infix 4 %=

(%|) = relation "divides"

-- associates:
(%=) = (\ a b -> a %| b /\ b %| a)

decls :: [Decl]
decls =
    -- Commutative ring axiom'ioms
    [ axiom' $ forall' $ commutative (+)
    , axiom' $ forall' $ commutative (*)
    , axiom' $ forall' $ associative (+)
    , axiom' $ forall' $ associative (*)
    , axiom' $ forall' $ distributes (*) (+)
    , axiom' $ forall' $ identity (+) zero
    , axiom' $ forall' $ identity (*) one
    , axiom' $ forall' $ \ x -> x + (neg x) === zero
    , axiom' $ forall' $ isZero (*) zero

    -- Integral domain
    , axiom' $ forall' $ \ x y -> x * y === zero ==> (x === zero \/ y === zero)

    -- Division ring
    , axiom' $ forall' $ \ a b -> a %| b <=> (exists' $ \ x -> b === x * a)
    -- ok:
    , axiom' $ forall' $ \ a b -> Folly.neg (a %| b) <=> (forall' $ \ x -> b != x * a)

    -- GCD ring
    , axiom' $ forall' $ \ a b c -> c %| gcd a b <=> c %| a /\ c %| b

    -- ok:
    , axiom' $ forall' $ \ x -> x %| x
    -- ok:
    , axiom' $ forall' $ \ x y z -> x %| y /\ y %| z ==> x %| z
    -- ok:
    , axiom' $ forall' $ \ a b c -> a %| b /\ a %| c ==> a %| (b + c)
    -- counterexample found, ok:
--   , axiom' $ forall' $ \ a b -> a %| b ==> b %| a

    -- ok:
    , axiom' $ forall' $ associativeOver (%=) gcd
    -- ok:
    , axiom' $ forall' $ commutativeOver (%=) gcd

    -- Bézout ring
    , axiom' $ forall' $ \ a b -> exists' $ \ x y -> a * x + b * y %= gcd a b

-- Lorenzini:
    , conjecture' $ forall' $ \ a b c ->
         (exists' $ \ x y z -> a * x + b * y + c * z %= one) ==>
         (exists' $ \ p q x' y' -> p * a * x' + (p * b + q * c) * y' %= one)

-- Lombardi:
{-
    , conjecture' $ forall' $ \ a b c ->
        (exists' $ \ x y z -> a * x + b * y + c * z %= one) ==>
        (exists' $ \ p q x' y' -> p * x' * a + q * x' * b + q * y' * c %= one)
-}
    ]

main :: IO ()
main = outputTPTP decls

