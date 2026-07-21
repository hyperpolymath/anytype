#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
# Golden tests for the anytype-check process-boundary seam: verdict lines
# AND exit codes (which are the wire contract — Abi.Types.verdictCode).
# Build first: idris2 --build anytype-cli.ipkg  (just test does this).
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/.."

BIN=./build/exec/anytype-check
[ -x "$BIN" ] || { echo "FAIL: $BIN not built (run: just test)"; exit 1; }

fails=0

case_check() {
  local desc="$1" disc="$2" term="$3" want_exit="$4" want_prefix="$5"
  local out rc
  set +e
  out="$(echo "$term" | "$BIN" --discipline "$disc" 2>&1)"
  rc=$?
  set -e
  if [ "$rc" -eq "$want_exit" ] && [[ "$out" == "$want_prefix"* ]]; then
    echo "  PASS  $desc"
  else
    echo "  FAIL  $desc (want exit=$want_exit '$want_prefix...', got exit=$rc '$out')"
    fails=$((fails + 1))
  fi
}

echo "=== anytype-check seam golden tests ==="
case_check "affine: use once accepted"        affine '(lam 1 bool (var 0))' 0 "ACCEPT"
case_check "affine: drop accepted"            affine '(lam 1 bool tt)' 0 "ACCEPT"
case_check "affine: double use rejected"      affine '(lam 1 bool (pair (var 0) (var 0)))' 1 "REJECT"
case_check "exact: drop rejected (the split)" exact  '(lam 1 bool tt)' 1 "REJECT"
case_check "exact: double use at 2 accepted"  exact  '(lam 2 bool (pair (var 0) (var 0)))' 0 "ACCEPT"
case_check "conversion: (word (+ 2 3)) is Bits 5" affine '(word (+ 2 3))' 0 "ACCEPT Bits 5"
case_check "ill-formed input is exit 2"       affine 'garbage((' 2 "ILLFORMED"
case_check "ill-scoped term is exit 2"        affine '(var 0)' 2 "ILLFORMED"

echo
if [ "$fails" -gt 0 ]; then
  echo "RESULT: FAIL ($fails failure(s))"
  exit 1
fi
echo "RESULT: PASS"
