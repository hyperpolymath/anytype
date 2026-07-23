||| anytype L1+L2: the usage-counting bidirectional checker.
|||
||| Output-usage formulation (Atkey/QTT style): `infer` returns the type
||| together with a usage vector saying how heavily each free variable
||| was used. Grade accounting:
|||   Var i          — usage gone at i, gzero elsewhere
|||   App f x        — Uf `gadd` (q `gmul` Ux), scaling through the arrow
|||   Lam q A b      — admit iff computed usage of the binder `gleq` q
||| That single inequality is what makes the discipline pluggable:
||| under the affine order dropping a grade-1 binder passes (0 <= 1),
||| under the exact order it fails (0 /= 1). Same rule, distinct
||| disciplines.
|||
||| Conversion is invoked at exactly one place: the check/infer mode
||| switch in `check`.
module Anytype.Core.Check

import Data.Fin
import Data.Vect
import Anytype.Grade.Algebra
import Anytype.Core.Syntax
import Anytype.Core.Conversion

%default total

||| Typing context: declared types of the free variables (grades live
||| on binders; usage is computed, not declared, for the context).
public export
Ctx : Type -> Nat -> Type
Ctx g n = Vect n (Ty g)

||| Computed usage: one grade per free variable.
public export
Usage : Type -> Nat -> Type
Usage g n = Vect n g

zeroU : GradeAlgebra g -> (n : Nat) -> Usage g n
zeroU alg n = replicate n alg.gzero

oneAt : GradeAlgebra g -> {n : Nat} -> Fin n -> Usage g n
oneAt alg FZ = alg.gone :: zeroU alg _
oneAt alg (FS i) = alg.gzero :: oneAt alg i

addU : GradeAlgebra g -> Usage g n -> Usage g n -> Usage g n
addU alg = zipWith alg.gadd

scaleU : GradeAlgebra g -> g -> Usage g n -> Usage g n
scaleU alg q = map (alg.gmul q)

mutual
  ||| Synthesise a type and a usage vector.
  public export
  infer : GradeAlgebra g -> {n : Nat} -> Ctx g n -> Term g n ->
          Either CheckError (Ty g, Usage g n)
  infer alg ctx (Var i) = Right (index i ctx, oneAt alg i)
  infer alg ctx (Lam q a body) = do
    (tb, u) <- infer alg (a :: ctx) body
    let (u0 :: rest) = u
    if alg.gleq u0 q
      then Right (TArr q a tb, rest)
      else Left UsageViolation
  infer alg ctx (App f x) = do
    (tf, uf) <- infer alg ctx f
    case tf of
      TArr q a b => do
        ux <- check alg ctx x a
        Right (b, addU alg uf (scaleU alg q ux))
      _ => Left NotAFunction
  infer alg ctx (Pair s t) = do
    (ts, us) <- infer alg ctx s
    (tt, ut) <- infer alg ctx t
    Right (TProd ts tt, addU alg us ut)
  infer alg ctx (LetPair p body) = do
    (tp, up) <- infer alg ctx p
    case tp of
      TProd a b => do
        -- components bound at grade gone: FS FZ = first, FZ = second
        (tr, u) <- infer alg (b :: a :: ctx) body
        let (u1 :: u0 :: rest) = u
        if alg.gleq u0 alg.gone && alg.gleq u1 alg.gone
          then Right (tr, addU alg up rest)
          else Left UsageViolation
      _ => Left NotAPair
  infer alg ctx TT = Right (TUnit, zeroU alg n)
  infer alg ctx (BLit _) = Right (TBool, zeroU alg n)
  infer alg ctx (WordLit w) = Right (TBits w, zeroU alg n)

  ||| Check against an expected type: infer, then normalise-and-compare.
  ||| This is the single conversion site.
  public export
  check : GradeAlgebra g -> {n : Nat} -> Ctx g n -> Term g n -> Ty g ->
          Either CheckError (Usage g n)
  check alg ctx t ty = do
    (ty', u) <- infer alg ctx t
    if convertible alg ty' ty
      then Right u
      else Left TypeMismatch
