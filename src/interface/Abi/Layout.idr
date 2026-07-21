-- SPDX-License-Identifier: MPL-2.0
-- Copyright (c) Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
||| ABI Layout Verification
|||
||| Formal proofs about memory layout, alignment, and padding for the
||| C-compatible structs anytype actually passes across its seam. The
||| generic machinery (Divides, StructLayout, FieldsAligned) is inherited
||| from the RSR template; the layouts proven at the bottom are anytype's
||| own request/response structs.

module Abi.Layout

import Abi.Types
import Data.Vect
import Data.So

%default total

--------------------------------------------------------------------------------
-- Alignment Invariants
--------------------------------------------------------------------------------

||| Predicate: n divides m
public export
data Divides : (n, m : Nat) -> Type where
  MkDivides : (k : Nat) -> (0 prf : m = k * n) -> Divides n m

||| Implementation of divides for common sizes
public export
div8_24 : Divides 8 24
div8_24 = MkDivides 3 Refl

public export
div4_0 : Divides 4 0
div4_0 = MkDivides 0 Refl

public export
div8_8 : Divides 8 8
div8_8 = MkDivides 1 Refl

public export
div8_16 : Divides 8 16
div8_16 = MkDivides 2 Refl

||| Calculate padding required for an offset to meet alignment
public export
paddingFor : (offset : Nat) -> (alignment : Nat) -> Nat
paddingFor offset 0 = 0
paddingFor offset alignment =
  let m = offset `mod` alignment in
  if m == 0
    then 0
    else alignment `minus` m

||| Align a size up to the next multiple of alignment
public export
alignUp : (size : Nat) -> (alignment : Nat) -> Nat
alignUp size alignment =
  size + paddingFor size alignment

--------------------------------------------------------------------------------
-- Struct Model
--------------------------------------------------------------------------------

||| Representation of a single field in a struct
public export
record Field where
  constructor MkField
  name : String
  offset : Nat
  size : Nat
  alignment : Nat

||| Valid memory layout for a C struct
public export
record StructLayout where
  constructor MkStructLayout
  {n : Nat}
  fields : Vect n Field
  totalSize : Nat
  alignment : Nat
  {auto 0 aligned : Divides alignment totalSize}

--------------------------------------------------------------------------------
-- Compliance Predicates
--------------------------------------------------------------------------------

||| Proof that all fields in a struct are correctly aligned
public export
data FieldsAligned : Vect n Field -> Type where
  NoFields : FieldsAligned []
  ConsField :
    (f : Field) ->
    (rest : Vect n Field) ->
    (0 prf : Divides f.alignment f.offset) ->
    FieldsAligned rest ->
    FieldsAligned (f :: rest)

||| Predicate: Struct is C-ABI compliant
public export
data CABICompliant : StructLayout -> Type where
  CABIOk : (l : StructLayout) ->
           (0 prf : FieldsAligned l.fields) ->
           CABICompliant l

--------------------------------------------------------------------------------
-- anytype wire structs
--------------------------------------------------------------------------------

div1_0 : Divides 1 0
div1_0 = MkDivides 0 Refl

div4_4 : Divides 4 4
div4_4 = MkDivides 1 Refl

||| anytype_request_t on 64-bit targets:
|||   struct { uint8_t discipline; /* pad 3 */ uint32_t term_len;
|||            const uint8_t *term_utf8; }
||| Size 16, alignment 8. The Zig side asserts the same layout with
||| comptime @sizeOf/@offsetOf checks against these numbers.
public export
requestLayout : StructLayout
requestLayout =
  MkStructLayout
    [ MkField "discipline" 0 1 1
    , MkField "term_len" 4 4 4
    , MkField "term_utf8" 8 8 8
    ]
    16
    8
    {aligned = div8_16}

public export
requestLayoutValid : CABICompliant Abi.Layout.requestLayout
requestLayoutValid = CABIOk Abi.Layout.requestLayout (
  ConsField (MkField "discipline" 0 1 1) _ div1_0 (
  ConsField (MkField "term_len" 4 4 4) _ div4_4 (
  ConsField (MkField "term_utf8" 8 8 8) _ div8_8 (
  NoFields))))

||| anytype_response_t on 64-bit targets:
|||   struct { uint8_t verdict; /* pad 3 */ uint32_t msg_len;
|||            const uint8_t *msg_utf8; }
||| Size 16, alignment 8.
public export
responseLayout : StructLayout
responseLayout =
  MkStructLayout
    [ MkField "verdict" 0 1 1
    , MkField "msg_len" 4 4 4
    , MkField "msg_utf8" 8 8 8
    ]
    16
    8
    {aligned = div8_16}

public export
responseLayoutValid : CABICompliant Abi.Layout.responseLayout
responseLayoutValid = CABIOk Abi.Layout.responseLayout (
  ConsField (MkField "verdict" 0 1 1) _ div1_0 (
  ConsField (MkField "msg_len" 4 4 4) _ div4_4 (
  ConsField (MkField "msg_utf8" 8 8 8) _ div8_8 (
  NoFields))))
