#!/usr/bin/env bash
# Count open proof obligations in Goals/ (lines containing sorry inside theorem proofs).
set -euo pipefail
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT"

count=$(rg -c '\bsorry\b' -g 'Goals/**/*.lean' . 2>/dev/null | awk -F: '{s+=$2} END {print s+0}')
files=$(rg -l '\bsorry\b' -g 'Goals/**/*.lean' . 2>/dev/null | wc -l | tr -d ' ')
echo "open_goals: ${count}"
echo "goal_files: ${files}"
by_topic=$(rg -c '\bsorry\b' -g 'Goals/**/*.lean' . 2>/dev/null | sed 's|^\./Goals/||;s|/.*||' | sort | uniq -c | sort -k2 || true)
echo "by_topic:"
echo "$by_topic"