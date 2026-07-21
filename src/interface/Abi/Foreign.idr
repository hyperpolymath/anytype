-- SPDX-License-Identifier: MPL-2.0
-- Copyright (c) Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
||| anytype FFI surface.
|||
||| Replaces the RSR template's generic librsr binding. The C symbol
||| declared here is what the Zig side (src/interface/ffi) exports; the
||| MVP transport behind it is a spawned `anytype-check` process — see
||| src/interface/ffi/README.adoc. In-process linkage of the kernel
||| (RefC backend) is future work; this declaration is the seam contract,
||| stated so both sides agree on one signature.
module Abi.Foreign

import Abi.Types

%default total

||| Raw seam call: check `term` (UTF-8 S-expression, NUL-terminated)
||| under the discipline byte. Returns a verdict code (see
||| Abi.Types.verdictCode). Provided by libanytype (Zig).
%foreign "C:anytype_check,libanytype"
prim__anytypeCheck : Bits8 -> String -> PrimIO Bits8

||| Safe wrapper: typed discipline in, decoded verdict out.
||| A code outside verdictCode's range is reported as VIllFormed —
||| the seam never invents an acceptance.
export
anytypeCheck : Discipline -> String -> IO Verdict
anytypeCheck d term = do
  code <- primIO (prim__anytypeCheck (disciplineCode d) term)
  pure (case code of
          0 => VAccepted
          1 => VRejected
          _ => VIllFormed)
