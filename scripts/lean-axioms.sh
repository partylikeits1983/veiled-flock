#!/bin/bash
# Audit the axioms of every theorem exported by the Flockzk Lean library.
#
# `lake build` succeeding does not by itself prove the development is free of
# extra axioms (`sorry` compiles to `sorryAx`; a stray `axiom` declaration
# would also pass). This script generates `#print axioms` for every theorem
# declared in lean/Flockzk/*.lean and fails unless each depends on at most
# the three standard axioms: propext, Classical.choice, Quot.sound.
#
# Usage: scripts/lean-axioms.sh   (run from the repo root; needs `lake build`
# to have succeeded first so the .olean files exist)
set -euo pipefail

cd "$(dirname "$0")/../lean"

# Extract declared theorem names. All Flockzk theorems live in namespace
# FlockZk; `section` blocks (e.g. PMF) do not change the fully-qualified name.
names=$(grep -hE '^theorem [A-Za-z_]' Flockzk/*.lean | awk '{print $2}' | sort -u)

if [ -z "$names" ]; then
  echo "lean-axioms: no theorems found — extraction broken?" >&2
  exit 1
fi

audit_file=$(mktemp -t flockzk-axioms-XXXXXX).lean
trap 'rm -f "$audit_file"' EXIT

{
  echo "import Flockzk"
  for n in $names; do
    echo "#print axioms FlockZk.$n"
  done
} > "$audit_file"

out=$(lake env lean "$audit_file" 2>&1) || {
  echo "$out"
  echo "lean-axioms: FAILED — lean could not elaborate the audit file" >&2
  exit 1
}

echo "$out"

# Every line is either "'X' does not depend on any axioms" or
# "'X' depends on axioms: [a, b, c]". Extract every axiom name mentioned and
# diff against the allowed set.
bad=$(echo "$out" \
  | grep -oE 'depends on axioms: \[[^]]*\]' \
  | sed -E 's/depends on axioms: \[//; s/\]//' \
  | tr ',' '\n' | tr -d ' ' | sort -u \
  | grep -vE '^(propext|Classical\.choice|Quot\.sound)$' || true)

count=$(echo "$names" | wc -l | tr -d ' ')
if [ -n "$bad" ]; then
  echo "lean-axioms: FAILED — non-standard axioms found:" >&2
  echo "$bad" >&2
  exit 1
fi

echo "lean-axioms: OK — $count theorems depend only on propext / Classical.choice / Quot.sound"
