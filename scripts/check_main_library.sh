#!/usr/bin/env bash
# Fail if the main library contains sorry or disallowed axioms.
set -euo pipefail
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT"

MAIN_GLOB="DstDiophantine/**/*.lean"

# Match proof obligations only (ignore docstrings that mention the word sorry).
SORRY_PAT='(^|[[:space:]])(by[[:space:]]+)?sorry[[:space:]]*$|:= by sorry'
if rg -q "$SORRY_PAT" -g "$MAIN_GLOB" .; then
  echo "error: sorry found in main library (DstDiophantine/)"
  rg "$SORRY_PAT" -g "$MAIN_GLOB" . || true
  exit 1
fi

# Eight explicit classical axioms permitted (see README / site/lean.html).
ALLOWED=(
  sumTwoCubesNotPerfectPower
  sumTwoFifthsNotSeventhOrNineteenth
  darmonMerelCube
  eulerAffineCubeAddTwo
  fermatLastTheorem
  fermatSignatureNN5
  mihailescu
  siksekStoll345
)

while IFS= read -r line; do
  name=$(echo "$line" | sed -n 's/^[[:space:]]*axiom[[:space:]]\([^[:space:]:]*\).*/\1/p')
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
done < <(rg '^[[:space:]]*axiom ' -g "$MAIN_GLOB" . || true)

if rg -q '^[[:space:]]*import[[:space:]]+Goals' -g "$MAIN_GLOB" .; then
  echo "error: main library must not import Goals"
  rg '^[[:space:]]*import[[:space:]]+Goals' -g "$MAIN_GLOB" . || true
  exit 1
fi

echo "check_main_library: ok (no sorry; axioms allowlisted; no Goals import)"