module Main where

import Folly.DSL hiding (neg)
import qualified Folly.DSL as Folly
import Folly.TPTP

import Control.Monad

import Prelude hiding (succ,(+),(-),pred,(*),gcd)

zero = constant "zero"
one  = constant "one"
(+)  = binary   "plus"
(*)  = binary   "mul"
neg  = unary    "neg"
gcd  = binary   "gcd"

infixl 5 +
infixl 5 -
infixl 6 *
infix 4 %=
infix 4 %|

(%|) = relation "divides"

-- associates:
(%=) = (\ a b -> a %| b /\ b %| a)

coprime a b = gcd a b %| one

a - b = a + neg b

decls :: [Decl]
decls =
    -- Commutative ring axioms
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

    -- Ring with explicit divisibilty
    , axiom' $ forall' $ \ a b -> a %| b <=> (exists' $ \ x -> b === x * a)

    -- GCD ring
    , axiom' $ forall' $ \ a b c -> c %| gcd a b <=> c %| a /\ c %| b

    -- Bézout ring
    , axiom' $ forall' $ \ a b -> exists' $ \ x y -> a * x + b * y %= gcd a b

    ]

inv_units = (,) "inv_units" $
    forall' $ \ x ->
        x %| one ==>
        (exists' $ \ y -> x * y === one /\ y * x === one)

regular = (,) "regular" $
    forall' $ \ a u v ->
        a != zero ==>
        a * u === a * v ==>
        u === v

bezoutmatrix' = (,) "bezoutmatrix'" $
    forall' $ \ a b ->
        gcd a b != zero ==>
        (exists' $ \ x y a1 b1 g ->
                   x * a1 + y * b1 === one
                /\ b1 * a === a1 * b
                /\ b === g * b1
                /\ a === g * a1
                /\ a * x + b * y === g
                /\ g %= gcd a b
                /\ b %= gcd a b * b1
                /\ a %= gcd a b * a1
            )

bezoutmatrix = (,) "bezoutmatrix" $
    forall' $ \ a b ->
        gcd a b != zero ==>
        (exists' $ \ x y a1 b1 ->
                   x * a1 + y * b1 %= one
                /\ b1 * a %= a1 * b
                /\ b %= gcd a b * b1
                /\ a %= gcd a b * a1
                /\ a * x + b * y %= gcd a b
                {-
                /\ gcd a b %= gcd a b
                /\ b %= gcd a b * b1
                /\ a %= gcd a b * a1
                -}
            )


top = (,) "top" $ forall' $ \ a -> a === a

{-
    -- ok:
    , axiom' $ forall' $ \ a b -> Folly.neg (a %| b) <=> (forall' $ \ x -> b != x * a)
    -}
{-
    -- ok:
    , axiom' $ forall' $ \ x -> x %| x
    -- ok:
    , axiom' $ forall' $ \ x y z -> x %| y /\ y %| z ==> x %| z
    -- ok:
    , axiom' $ forall' $ \ a b c -> a %| b /\ a %| c ==> a %| (b + c)
    -- counterexample found, ok:
--    , conjecture'  $ forall' $ \ a b -> a %| b ==> b %| a
--    -}

{-
    -- ok:
    , axiom' $ forall' $ associativeOver (%=) gcd
    -- ok:
    , axiom' $ forall' $ commutativeOver (%=) gcd
    -}


helmer = (,) "helmer" $
    forall' $ \ a b -> a != zero ==>
    (exists' $ \ r s -> a === r * s /\ coprime r b /\
        (forall' $ \ d -> d %| s ==> coprime d b ==> d %| one))

cyril = (,) "cyril" $
    forall' $ \ a b -> a != zero ==>
    (exists' $ \ r -> r %| a /\ coprime r b /\
        (forall' $ \ d -> d %| a ==> coprime d b ==> d %| r))

kaplansky = (,) "kaplansky" $
    forall' $ \ a b c ->
        gcd a (gcd b c) %| one ==>
        (exists' $ \ p q -> gcd (p * a) (p * b + q * c) %| one)


lorenzini = (,) "lorenzini" $
    forall' $ \ a b c ->
         (exists' $ \ x y z -> a * x + b * y + c * z %= one) ==>
         (exists' $ \ p q x' y' -> p * a * x' + (p * b + q * c) * y' %= one)

lombardi = (,) "lombardi" $
    forall' $ \ a b c ->
        (exists' $ \ x y z -> a * x + b * y + c * z %| one) ==>
        (exists' $ \ p q x' y' -> p * x' * a + p * y' * b + q * y' * c %| one)

lombardi_cyril = (,) "lombardi_cyril" $
    forall' $ \ a b c ->
        exists' $ \ p q ->
            (exists' $ \ x y z -> a * x + b * y + c * z %| one) ==>
            (exists' $ \ x' y' -> p * x' * a + p * y' * b + q * y' * c %| one)

main :: IO ()
main = do
    forM_ tests $ \ ((ax_name,ax),(conj_name,conj)) ->
        writeTPTP (ax_name ++ "_implies_" ++ conj_name)
            (decls ++ [axiom' ax,conjecture' conj])
  where
    tests =
        [ cyril ===> lombardi_cyril
        , cyril ===> kaplansky
        , cyril ===> helmer
        , helmer ===> cyril
        , kaplansky ===> lombardi_cyril
        , lombardi_cyril ===> kaplansky
        , top ===> regular
        , top ===> bezoutmatrix
        , regular ===> bezoutmatrix
        , top ===> bezoutmatrix'
        , regular ===> bezoutmatrix'
        , top ===> inv_units
        -- open problems:
        , top ===> lorenzini
        , top ===> lombardi
        , top ===> lombardi_cyril
        ]

    (===>) = (,)

