#!/usr/bin/env bash
# Fail if the main library contains sorry or disallowed axioms.
set -euo pipefail
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT"

LEAN_FILES="$(find DstDiophantine -name '*.lean' -type f)"

# Match proof obligations only (ignore docstrings that mention the word sorry).
SORRY_PAT='(^|[[:space:]])(by[[:space:]]+)?sorry[[:space:]]*$|:= by sorry'
if grep -nE "$SORRY_PAT" $LEAN_FILES 2>/dev/null | grep -q .; then
  echo "error: sorry found in main library (DstDiophantine/)"
  grep -nE "$SORRY_PAT" $LEAN_FILES 2>/dev/null || true
  exit 1
fi

# Twelve explicit classical axioms permitted (see README / site/lean.html).
ALLOWED=(
  anniSiksekDoublePrimeSum
  bennettEllenbergNg
  sumTwoCubesNotPerfectPower
  sumTwoFifthsNotSeventhOrNineteenth
  sumTwoFifthsNotStollPrime
  darmonMerelCube
  eulerAffineCubeAddTwo
  fermatLastTheorem
  fermatSignatureNN5
  michaudJacobsPrimeSeventeenth
  mihailescu
  siksekStoll345
)

while IFS= read -r line; do
  [[ -z "$line" ]] && continue
  name=$(echo "$line" | sed -n 's/^[[:space:]]*axiom[[:space:]]\([A-Za-z_][A-Za-z0-9_'\'']*\).*/\1/p')
  [[ -z "$name" ]] && continue
  ok=0
  for a in "${ALLOWED[@]}"; do
    if [[ "$name" == "$a" ]]; then ok=1; break; fi
  done
  if [[ "$ok" -eq 0 ]]; then
    echo "error: disallowed axiom in main library: $name"
    echo "$line"
    exit 1
  fi
done < <(grep -hE '^[[:space:]]*axiom[[:space:]]+[A-Za-z_][A-Za-z0-9_'\'']*' $LEAN_FILES 2>/dev/null || true)

if grep -hE '^[[:space:]]*import[[:space:]]+Goals' $LEAN_FILES 2>/dev/null | grep -q .; then
  echo "error: main library must not import Goals"
  grep -nE '^[[:space:]]*import[[:space:]]+Goals' $LEAN_FILES 2>/dev/null || true
  exit 1
fi

echo "check_main_library: ok (no sorry; axioms allowlisted; no Goals import)"