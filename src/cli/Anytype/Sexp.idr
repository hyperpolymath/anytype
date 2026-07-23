||| Total S-expression reader for the anytype seam wire format.
|||
||| Grammar (one term per input):
|||   term  := (lam <grade> <ty> <term>) | (app <term> <term>)
|||          | (pair <term> <term>) | (letpair <term> <term>)
|||          | (var <nat>) | (word <tnat>) | tt | true | false
|||   ty    := unit | bool | (bits <tnat>)
|||          | (arr <grade> <ty> <ty>) | (prod <ty> <ty>)
|||   tnat  := <nat> | (+ <tnat> <tnat>) | (* <tnat> <tnat>)
||| Grades are discipline-specific atoms: affine 0|1|w, exact <nat>.
|||
||| Everything here is `%default total`: the tokeniser is structural on
||| the character list and the reader burns explicit fuel (the token
||| count), so the seam cannot hang on malformed input.
module Anytype.Sexp

import Data.String
import Data.Fin
import Anytype.Kernel

%default total

data Tok = TOpen | TClose | TAtom String

flush : List Char -> List Tok -> List Tok
flush [] ts = ts
flush acc ts = TAtom (pack (reverse acc)) :: ts

tokGo : List Char -> List Char -> List Tok
tokGo acc [] = flush acc []
tokGo acc (c :: cs) =
  if c == '(' then flush acc (TOpen :: tokGo [] cs)
  else if c == ')' then flush acc (TClose :: tokGo [] cs)
  else if isSpace c then flush acc (tokGo [] cs)
  else tokGo (c :: acc) cs

tokenise : String -> List Tok
tokenise s = tokGo [] (unpack s)

public export
data SExp = SAtom String | SList (List SExp)

mutual
  readOne : (fuel : Nat) -> List Tok -> Maybe (SExp, List Tok)
  readOne Z _ = Nothing
  readOne (S _) (TAtom a :: r) = Just (SAtom a, r)
  readOne (S f) (TOpen :: r) = do
    (xs, r') <- readMany f r
    pure (SList xs, r')
  readOne _ _ = Nothing

  readMany : (fuel : Nat) -> List Tok -> Maybe (List SExp, List Tok)
  readMany Z _ = Nothing
  readMany (S _) (TClose :: r) = Just ([], r)
  readMany (S f) toks = do
    (x, r) <- readOne f toks
    (xs, r') <- readMany f r
    pure (x :: xs, r')

||| Read exactly one S-expression covering the whole input.
public export
readSexp : String -> Maybe SExp
readSexp s =
  let toks = tokenise s in
  case readOne (S (length toks)) toks of
    Just (e, []) => Just e
    _ => Nothing

parseTNat : SExp -> Maybe TNat
parseTNat (SAtom s) = map tnatOfNat (parsePositive s)
parseTNat (SList [SAtom "+", a, b]) =
  [| NPlus (parseTNat a) (parseTNat b) |]
parseTNat (SList [SAtom "*", a, b]) =
  [| NMul (parseTNat a) (parseTNat b) |]
parseTNat _ = Nothing

parseTy : (pg : String -> Maybe g) -> SExp -> Maybe (Ty g)
parseTy _ (SAtom "unit") = Just TUnit
parseTy _ (SAtom "bool") = Just TBool
parseTy _ (SList [SAtom "bits", w]) = map TBits (parseTNat w)
parseTy pg (SList [SAtom "arr", SAtom q, a, b]) =
  [| TArr (pg q) (parseTy pg a) (parseTy pg b) |]
parseTy pg (SList [SAtom "prod", a, b]) =
  [| TProd (parseTy pg a) (parseTy pg b) |]
parseTy _ _ = Nothing

||| Scope-checked term reader: de Bruijn indices are bounds-checked
||| against `n` as they are read, so an ill-scoped input is Nothing,
||| never a crash.
public export
parseTerm : (pg : String -> Maybe g) -> (n : Nat) -> SExp ->
            Maybe (Term g n)
parseTerm _ n (SList [SAtom "var", SAtom k]) = do
  kn <- parsePositive k
  i <- natToFin kn n
  pure (Var i)
parseTerm pg n (SList [SAtom "lam", SAtom q, ty, body]) =
  [| Lam (pg q) (parseTy pg ty) (parseTerm pg (S n) body) |]
parseTerm pg n (SList [SAtom "app", f, x]) =
  [| App (parseTerm pg n f) (parseTerm pg n x) |]
parseTerm pg n (SList [SAtom "pair", s, t]) =
  [| Pair (parseTerm pg n s) (parseTerm pg n t) |]
parseTerm pg n (SList [SAtom "letpair", p, body]) =
  [| LetPair (parseTerm pg n p) (parseTerm pg (S (S n)) body) |]
parseTerm _ _ (SAtom "tt") = Just TT
parseTerm _ _ (SAtom "true") = Just (BLit True)
parseTerm _ _ (SAtom "false") = Just (BLit False)
parseTerm _ n (SList [SAtom "word", w]) = map WordLit (parseTNat w)
parseTerm _ _ _ = Nothing

||| Affine grades: 0 | 1 | w.
public export
affineGrade : String -> Maybe Q
affineGrade "0" = Just Q0
affineGrade "1" = Just Q1
affineGrade "w" = Just QW
affineGrade _ = Nothing

||| Exact grades: any natural number.
public export
exactGrade : String -> Maybe Nat
exactGrade = parsePositive

||| Parse a closed term from wire text.
public export
parseClosed : (pg : String -> Maybe g) -> String -> Maybe (Term g 0)
parseClosed pg s = readSexp s >>= parseTerm pg 0
