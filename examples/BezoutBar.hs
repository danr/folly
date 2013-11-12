{-# OPTIONS_GHC -fno-warn-missing-signatures #-}
module Main where

import Folly.DSL hiding (neg)
import qualified Folly.DSL as Folly
import Folly.TPTP

import Control.Monad
import Data.List

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

neg_involutive = (,) "neg_involutive" $ forall' $ \x -> neg (neg x) === x

gcd_square = (,) "gcd_square" $
  forall' $ \ x y ->
    gcd (x * x) (y * y) %= (gcd x y) * (gcd x y)

gauss_lemma = (,) "gauss_lemma" $
  forall' $ \ x y z ->
    x %| y * z /\ coprime x z ==>
    x %| y

inv_units = (,) "inv_units" $
    forall' $ \ x ->
        x %| one ==>
        (exists' $ \ y -> x * y === one /\ y * x === one)

regular = (,) "regular" $
    forall' $ \ a u v ->
        a != zero ==>
        a * u === a * v ==>
        u === v

bezoutmatrix = (,) "bezoutmatrix" $
    forall' $ \ a b ->
        gcd a b != zero ==>
        (exists' $ \ x y a1 b1 ->
                   x * a1 + y * b1 === one
                /\ b1 * a === a1 * b)

neg_divides = (,) "neg_divides" $
    forall' $ \ a b -> Folly.neg (a %| b) <=> (forall' $ \ x -> b != x * a)

div_refl = (,) "div_refl" $ forall' $ \ x -> x %| x

div_trans = (,) "div_trans" $ forall' $ \ x y z -> x %| y /\ y %| z ==> x %| z

div_plus = (,) "div_plus" $ forall' $ \ a b c -> a %| b /\ a %| c ==> a %| (b + c)

-- countersatisfiable:
div_sym = (,) "div_sym" $ forall' $ \ a b -> a %| b ==> b %| a

gcd_assoc = ("gcd_assoc",forall' $ associativeOver (%=) gcd)

gcd_comm = ("gcd_comm",forall' $ commutativeOver (%=) gcd)

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
    forM_ tests $ \ (axioms,(conj_name,conj)) ->
        let (names,axs) = unzip axioms
        in  writeTPTP ((case names of
                            [] -> ""
                            [x] -> x ++ "_implies_"
                            xs  -> "lemmas_")
                            ++ conj_name)
               (decls ++ map axiom' axs ++ [conjecture' conj])
  where
    tests =
        [ cyril ===> lombardi_cyril
        , cyril ===> kaplansky
        , helmer ===> cyril
        , kaplansky ===> cyril
        , kaplansky ===> lombardi_cyril
        , lombardi_cyril ===> kaplansky
        , only regular
        , only bezoutmatrix       -- X
        , regular ===> bezoutmatrix   -- X
        , only inv_units

        , lemmas =&=> bezoutmatrix

        , only neg_divides
        , only div_refl
        , only div_trans
        , only div_plus
        , only div_sym            -- countersatisfiable

        , only neg_involutive

        , only gcd_assoc
        , only gcd_comm
        , only gcd_square
        , only gauss_lemma        -- X
        , gauss_lemma ===> gcd_square -- X

        -- "open" since this morning:
        , cyril ===> helmer
        -- open problems:
        , only kaplansky
        , only lombardi
        , only lombardi_cyril
        , lemmas =&=> kaplansky
        , lemmas =&=> lombardi
        , lemmas =&=> lombardi_cyril
        ]

    only    x = ([],x)
    x  ===> y = ([x],y)
    xs =&=> y = (xs,y)
    lemmas =
        [ neg_divides
        , div_refl
        , div_trans
        , div_plus
        , gcd_assoc
        , gcd_comm
        , gauss_lemma
        , gcd_square
        ]



bezoutmatrix_help1 = (,) "bezoutmatrix_help1" $
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

bezoutmatrix_help2 = (,) "bezoutmatrix_help2" $
    forall' $ \ a b ->
        gcd a b != zero ==>
        (exists' $ \ x y a1 b1 ->
                   x * a1 + y * b1 %= one
                /\ b1 * a %= a1 * b
                /\ b %= gcd a b * b1
                /\ a %= gcd a b * a1
                /\ a * x + b * y %= gcd a b
            )

