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

count=$(grep -rhoE '\bsorry\b' $GOAL_FILES 2>/dev/null | wc -l | tr -d ' ')
files=$(grep -rlE '\bsorry\b' $GOAL_FILES 2>/dev/null | wc -l | tr -d ' ')
echo "open_goals: ${count}"
echo "goal_files: ${files}"
echo "by_topic:"
grep -rlE '\bsorry\b' $GOAL_FILES 2>/dev/null |
  sed 's|^Goals/||;s|/.*||' |
  sort |
  uniq -c |
  sort -k2 || true