||| anytype L1: syntax of the MVP core — a bidirectional simply-graded
||| lambda calculus.
|||
||| The type-index language `TNat` deliberately has NO fixpoint or
||| recursion constructor: type-level computation is total *by
||| construction*, which is the MVP discharge of systemet's L1 totality
||| gate (a syntactic gate, not a termination analysis — see EXPLAINME).
|||
||| Terms are intrinsically scoped (de Bruijn via `Fin`), parameterised
||| by the grade carrier `g` because binders and arrows carry grades.
module Anytype.Core.Syntax

import Data.Fin

%default total

||| Total type-level naturals: the index language for `TBits`.
public export
data TNat : Type where
  NZ    : TNat
  NS    : TNat -> TNat
  NPlus : TNat -> TNat -> TNat
  NMul  : TNat -> TNat -> TNat

||| Types, parameterised by the grade carrier.
public export
data Ty : Type -> Type where
  TUnit : Ty g
  TBool : Ty g
  ||| An indexed family so conversion has real work to do:
  ||| `TBits (NPlus 2 3)` and `TBits 5` are convertible, not equal.
  TBits : TNat -> Ty g
  ||| Graded function arrow  q : A -> B.
  TArr  : g -> Ty g -> Ty g -> Ty g
  ||| Multiplicative pair.
  TProd : Ty g -> Ty g -> Ty g

||| Intrinsically scoped terms. No `if`: branching needs a join on
||| grades beyond systemet's stated semiring+order laws (post-MVP).
public export
data Term : Type -> Nat -> Type where
  Var     : Fin n -> Term g n
  ||| Binder carries its declared grade and domain type.
  Lam     : g -> Ty g -> Term g (S n) -> Term g n
  App     : Term g n -> Term g n -> Term g n
  Pair    : Term g n -> Term g n -> Term g n
  ||| Pattern-match consumption of a pair. The body sees the components
  ||| at de Bruijn indices FS FZ (first) and FZ (second), each bound at
  ||| grade `gone` (multiplicative elimination).
  LetPair : Term g n -> Term g (S (S n)) -> Term g n
  TT      : Term g n
  BLit    : Bool -> Term g n
  ||| Type-indexed word literal: `WordLit w : TBits w`, usage zero.
  ||| Exists so closed terms can exercise conversion at `TBits`.
  WordLit : TNat -> Term g n

||| Why the checker rejected a term.
public export
data CheckError : Type where
  NotAFunction   : CheckError
  NotAPair       : CheckError
  TypeMismatch   : CheckError
  ||| Computed usage of a binder exceeds its declared grade.
  UsageViolation : CheckError

public export
Show CheckError where
  show NotAFunction   = "not a function"
  show NotAPair       = "not a pair"
  show TypeMismatch   = "type mismatch"
  show UsageViolation = "usage violation"
