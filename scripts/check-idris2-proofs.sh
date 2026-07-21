#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
# Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <6759885+hyperpolymath@users.noreply.github.com>
#
# Type-check every Idris2 module in the repository.
#
# This script is the single source of truth for "does the Idris2 in this repo
# compile?".  Both CI (.github/workflows/idris2-proof.yml) and the Justfile
# (`just proof-check-idris2`) call it, so a green local run and a green CI run
# mean the same thing.
#
# Adapted from ideas-to-alphas scripts/check-idris2-proofs.sh, which documents
# why each rule exists.  The estate-wide failure mode it replaces: the old
# build/just/proofs.just recipe did `exit 0` when idris2 was absent, so every
# proof in this repo reported green on machines where nothing could check them.
# If you extend this script, the test to apply is not "does it pass?" but
# "have I watched it fail?".
#
# Three rules:
#   * A missing toolchain is a FAILURE, never a skip.
#   * Every module is checked from its own source root (module ABI.Foreign
#     lives at <root>/ABI/Foreign.idr; a wrong root fails on the name, not on
#     the real errors).
#   * A module that is not in the MANIFEST is an error.  New Idris2 anywhere
#     in the tree is gated by default; you cannot add an unchecked proof.
#
# Exit codes: 0 = all gated modules check and all quarantined modules still
# fail as expected; 1 = otherwise.

set -euo pipefail

cd "$(dirname "${BASH_SOURCE[0]}")/.."
ROOT="$PWD"

# --- MANIFEST -----------------------------------------------------------------
# Format: <source-root>|<module-path>|<gated|quarantine>|<extra idris2 args>|<note>
#
# gated      -- must type-check.  A failure fails this script and CI.
# quarantine -- known-broken RSR template stock, kept for reference.  Must
#               CONTINUE to fail; if one starts passing the script fails and
#               tells you to promote it, so the list cannot silently rot.
#               Verdicts measured 2026-07-21 under Idris2 0.7.0.
MANIFEST=(
  "src/kernel|Anytype/Grade/Algebra.idr|gated||L2 grade-algebra interface: laws are proof fields"
  "src/kernel|Anytype/Grade/Affine.idr|gated||{0,1,omega} instance mirroring affinescript lib/quantity.ml"
  "src/kernel|Anytype/Grade/Exact.idr|gated||exact-usage Nat instance: the distinct-discipline demo"
  "src/kernel|Anytype/Core/Syntax.idr|gated||graded STLC syntax; TNat total by construction"
  "src/kernel|Anytype/Core/Normalise.idr|gated||the L1 totality artefact"
  "src/kernel|Anytype/Core/Conversion.idr|gated||normalise-and-compare"
  "src/kernel|Anytype/Core/Check.idr|gated||usage-counting bidirectional checker"
  "src/kernel|Anytype/Kernel.idr|gated||public API"
  "src/interface|Abi/Types.idr|gated||ABI seam types"
  "src/interface|Abi/Layout.idr|gated||ABI layout proofs"
  "src/interface|Abi/Foreign.idr|gated||ABI FFI declarations"
  ".machine_readable/coaptation/core|Coaptation.idr|gated||coaptation skeleton; compiles, semantically a placeholder"
  "verification/tests/kernel|Tests/Main.idr|gated|-p anytype|golden matrix; needs anytype installed (just test does this)"
  "src/cli|Anytype/Sexp.idr|gated|-p anytype|total S-expression reader for the seam wire format"
  "src/cli|Anytype/Main.idr|gated|-p anytype -p anytype-abi|anytype-check entry point; exit codes = Abi.Types verdictCode"
  "verification/proofs/idris2|ABI/Foreign.idr|gated||the one template verification module that compiles"
  "verification/proofs/idris2|Types.idr|quarantine||RSR template stock, never compiled: LTE needs Data.Nat"
  "verification/proofs/idris2|ABI/Platform.idr|quarantine||template stock: LTE needs Data.Nat, then undefined lteRefl"
  "verification/proofs/idris2|ABI/Layout.idr|quarantine||template stock: NonZero/modNatNZ need Data.Nat"
  "verification/proofs/idris2|ABI/Pointers.idr|quarantine||template stock: erased .nonNull projected into a value position"
  "verification/proofs/idris2|ABI/Compliance.idr|quarantine||depends on quarantined ABI.Layout"
)

# --- toolchain: absent means FAIL, never skip ---------------------------------
if ! command -v idris2 >/dev/null 2>&1; then
  cat >&2 <<'EOF'
FAIL: idris2 not found on PATH.

This is deliberately fatal.  The recipe this script replaces did `exit 0` here
with "SKIP: idris2 not installed", which meant every proof in this repo
reported green on machines where nothing could check them.  An unrunnable gate
that reports success is worse than no gate: it manufactures false confidence.

Install Idris2 0.7.0, or run this in CI where the workflow installs it.
EOF
  exit 1
fi

echo "=== Idris2 proof check ==="
idris2 --version
echo

# --- verdict ------------------------------------------------------------------
# `idris2 --check` EXITS 0 ON A MISSING IMPORT while printing "Error: Module X
# not found".  Testing $? alone is therefore unsound.  We require BOTH a zero
# exit AND no "Error:" in the output.
check_module() {
  local root="$1" rel="$2" args="$3" out rc
  set +e
  # shellcheck disable=SC2086
  out="$(cd "$ROOT/$root" && idris2 $args --check "$rel" 2>&1)"
  rc=$?
  set -e
  if [ "$rc" -eq 0 ] && ! grep -q '^Error:' <<<"$out"; then
    LAST_OUT=""
    return 0
  fi
  LAST_OUT="$out"
  return 1
}

fails=0
unexpected_pass=0

for entry in "${MANIFEST[@]}"; do
  IFS='|' read -r root rel status args note <<<"$entry"
  printf '  %-34s %-22s ' "$root" "$rel"

  if check_module "$root" "$rel" "$args"; then
    if [ "$status" = "gated" ]; then
      echo "PASS"
    else
      echo "PASS -- UNEXPECTED"
      echo "      This module is marked 'quarantine' but now type-checks."
      echo "      Promote it to 'gated' in the MANIFEST and update PROOF-STATUS."
      unexpected_pass=$((unexpected_pass + 1))
    fi
  else
    if [ "$status" = "gated" ]; then
      echo "FAIL"
      printf '%s\n' "${LAST_OUT//$'\n'/$'\n        '}" | sed '1s/^/        /'
      fails=$((fails + 1))
    else
      echo "fail (quarantined, expected)"
      echo "        reason: $note"
    fi
  fi
done

# --- no unlisted Idris2 anywhere in the tree ----------------------------------
# The anti-recurrence rule: a module absent from the MANIFEST is an error, so
# new Idris2 is gated by default rather than by remembering.
echo
echo "=== manifest coverage ==="
listed="$(for e in "${MANIFEST[@]}"; do IFS='|' read -r r m _ _ _ <<<"$e"; echo "$r/$m"; done | sort)"
found="$(find . -name '*.idr' -not -path './.git/*' -not -path '*/build/*' -not -path './.claude/*' \
          | sed 's|^\./||' | sort)"
unlisted="$(comm -13 <(echo "$listed") <(echo "$found") || true)"
missing="$(comm -23 <(echo "$listed") <(echo "$found") || true)"

if [ -n "$unlisted" ]; then
  echo "FAIL: Idris2 modules present on disk but absent from the MANIFEST:"
  printf '  %s\n' "${unlisted//$'\n'/$'\n  '}"
  echo
  echo "  Every .idr in this repo must be listed in scripts/check-idris2-proofs.sh,"
  echo "  as 'gated' (it must compile) or 'quarantine' (known-broken, tracked)."
  fails=$((fails + 1))
fi

if [ -n "$missing" ]; then
  echo "FAIL: MANIFEST lists modules that do not exist (stale entries):"
  printf '  %s\n' "${missing//$'\n'/$'\n  '}"
  fails=$((fails + 1))
fi

[ -z "$unlisted$missing" ] && echo "  all $(echo "$found" | wc -l | tr -d ' ') .idr files accounted for"

echo
if [ "$fails" -gt 0 ] || [ "$unexpected_pass" -gt 0 ]; then
  echo "RESULT: FAIL ($fails failure(s), $unexpected_pass unexpected pass(es))"
  exit 1
fi
echo "RESULT: PASS -- all gated modules type-check; quarantined modules still fail as recorded"
