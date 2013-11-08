{-# LANGUAGE FlexibleInstances, TemplateHaskell, OverloadedStrings #-}
module Folly.TPTP where

import Text.PrettyPrint
import Folly.FOL


infixr 1 `hung`

hung :: Doc -> Doc -> Doc
a `hung` b = cat [a, nest 2 b]

ppDecl :: Decl -> Doc
ppDecl (Decl t s f) = cat ["fof" <> "(" <> ppStr s <> comma <> ppDeclType t <> comma
                          , nest 2 (ppForm f)
                          , ")" <> "."
                          ]

ppDeclType :: DeclType -> Doc
ppDeclType t = case t of
    Axiom      -> "axiom"
    Conjecture -> "conjecture"
    Question   -> "question"
    NegConj    -> "negated_conjecture"
    Lemma      -> "lemma"
    Hypothesis -> "hypothesis"
    Definition -> "definition"

-- TODO: make this escape variables properly when needed
ppStr :: String -> Doc
ppStr = text

pif :: Bool -> Doc -> Doc
pif True  = parens
pif False = id

ppForm :: Formula -> Doc
ppForm = go 0
  where
    go :: Int -> Formula -> Doc
    go i f0 = case f0 of
        EqOp t1 op t2 -> sep [ppTerm t1 <+> ppEqOp op,ppTerm t2]
        Rel s tms     -> function s (map ppTerm tms)
        Neg f         -> "~" `hung` go 5 f
        BinOp _ op _  -> pif (i > 0) $
            sep (punctuate (space <> ppBinOp op) (map (go 2) (collectBinOp op f0)))
        Quant q qs f   -> pif (i > 1) $
            ppQuant q <+> brackets (cat ((punctuate comma) (map ppStr qs))) <+> ":" <> space `hung` go 1 f

ppQuant :: Quant -> Doc
ppQuant q = case q of
    Forall -> "!"
    Exists -> "?"

ppBinOp :: BinOp -> Doc
ppBinOp op = case op of
    (:&)   -> "&"
    (:|)   -> "|"
    (:=>)  -> "=>"
    (:<=>) -> "<=>"

ppEqOp :: EqOp -> Doc
ppEqOp op = case op of
    (:==) -> "="
    (:!=) -> "!="

collectBinOp :: BinOp -> Formula -> [Formula]
collectBinOp (:=>)  (BinOp f1 (:=>) f2)  = [f1,f2]
collectBinOp (:<=>) (BinOp f1 (:<=>) f2) = [f1,f2]
collectBinOp op0 (BinOp f1 op f2)
    | op0 == op = collectBinOp op0 f1 ++ collectBinOp op0 f2
collectBinOp _   f = [f]

ppTerm :: Term -> Doc
ppTerm (Fun s tms) = function s (map ppTerm tms)
ppTerm (Var s)     = ppStr s

stringTPTP :: [Decl] -> String
stringTPTP = (++ "\n") . render . vcat . map ppDecl

writeTPTP :: FilePath -> [Decl] -> IO ()
writeTPTP file a = writeFile file (stringTPTP a)

outputTPTP :: [Decl] -> IO ()
outputTPTP = putStr . stringTPTP

csv :: [Doc] -> Doc
csv = inside "(" "," ")"

bsv :: [Doc] -> Doc
bsv = inside "[" "," "]"

inside :: Doc -> Doc -> Doc -> [Doc] -> Doc
inside _ _ _ []     = empty
inside l p r (x:xs) = cat (go (l <> x) xs)
  where
    go y []     = [y,r]
    go y (z:zs) = y : go (p <> z) zs

function :: String -> [Doc] -> Doc
function s [] = text s
function s xs = text s <> "(" `hung` (cat (punctuate "," xs) <> ")")



