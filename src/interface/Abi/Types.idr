-- SPDX-License-Identifier: MPL-2.0
-- Copyright (c) Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
||| anytype ABI wire types.
|||
||| This module used to be the RSR template's generic ABI demo; it now
||| defines anytype's actual seam surface: the discipline selector and
||| the verdict a kernel check returns, with machine-checked facts about
||| their byte encodings (codes are injective and decoding inverts
||| encoding, so the Zig side can trust a reverse lookup).
module Abi.Types

%default total

||| Which grade algebra the kernel should check under.
public export
data Discipline = DAffine | DExact

||| Wire encoding of a discipline.
public export
disciplineCode : Discipline -> Bits8
disciplineCode DAffine = 0
disciplineCode DExact = 1

||| The result of a kernel check, as seen across the ABI.
public export
data Verdict = VAccepted | VRejected | VIllFormed

||| Wire encoding of a verdict.
public export
verdictCode : Verdict -> Bits8
verdictCode VAccepted = 0
verdictCode VRejected = 1
verdictCode VIllFormed = 2

||| Decode a discipline byte (total; out-of-range is Nothing).
public export
disciplineOfCode : Bits8 -> Maybe Discipline
disciplineOfCode 0 = Just DAffine
disciplineOfCode 1 = Just DExact
disciplineOfCode _ = Nothing

-- Machine-checked encoding facts -------------------------------------------

||| Discipline codes are injective.
public export
disciplineCodeInjective : (d1, d2 : Discipline) ->
                          disciplineCode d1 = disciplineCode d2 -> d1 = d2
disciplineCodeInjective DAffine DAffine _ = Refl
disciplineCodeInjective DExact DExact _ = Refl
disciplineCodeInjective DAffine DExact Refl impossible
disciplineCodeInjective DExact DAffine Refl impossible

||| Verdict codes are injective.
public export
verdictCodeInjective : (v1, v2 : Verdict) ->
                       verdictCode v1 = verdictCode v2 -> v1 = v2
verdictCodeInjective VAccepted VAccepted _ = Refl
verdictCodeInjective VRejected VRejected _ = Refl
verdictCodeInjective VIllFormed VIllFormed _ = Refl
verdictCodeInjective VAccepted VRejected Refl impossible
verdictCodeInjective VAccepted VIllFormed Refl impossible
verdictCodeInjective VRejected VAccepted Refl impossible
verdictCodeInjective VRejected VIllFormed Refl impossible
verdictCodeInjective VIllFormed VAccepted Refl impossible
verdictCodeInjective VIllFormed VRejected Refl impossible

||| Decoding inverts encoding.
public export
disciplineRoundTrip : (d : Discipline) ->
                      disciplineOfCode (disciplineCode d) = Just d
disciplineRoundTrip DAffine = Refl
disciplineRoundTrip DExact = Refl
