#!/usr/bin/env bash
# Count open proof obligations in Goals/ (sorry in theorem proofs).
set -euo pipefail
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT"

GOAL_FILES="$(find Goals -name '*.lean' -type f 2>/dev/null || true)"

if [[ -z "$GOAL_FILES" ]]; then
  echo "open_goals: 0"
  echo "goal_files: 0"
  echo "by_topic:"
  exit 0
fi

# `True` is proved by `trivial` and does not state a claim.
if grep -nE '\bTrue :=' $GOAL_FILES; then
  echo "error: Goals must not use True as a statement" >&2
  exit 1
fi

count=$(grep -rhoE '\bby sorry\b' $GOAL_FILES 2>/dev/null | wc -l | tr -d ' ')
files=$(grep -rlE '\bby sorry\b' $GOAL_FILES 2>/dev/null | wc -l | tr -d ' ')
echo "open_goals: ${count}"
echo "goal_files: ${files}"
echo "by_file:"
grep -rlE '\bby sorry\b' $GOAL_FILES 2>/dev/null | sort | while read -r f; do
  n=$(grep -oE '\bby sorry\b' "$f" | wc -l | tr -d ' ')
  printf '%7s %s\n' "$n" "${f#Goals/}"
done