#!/bin/bash
# Audit the axioms of the legacy Flockzk theorems and the formal VEIL-FLOCK
# statistical-ZK theorem chain.
#
# `lake build` succeeding does not by itself prove the development is free of
# extra axioms (`sorry` compiles to `sorryAx`; a stray `axiom` declaration
# would also pass). This script generates `#print axioms` and fails unless
# each checked theorem depends on at most the three standard axioms: propext,
# Classical.choice, Quot.sound.
#
# Usage: scripts/lean-axioms.sh   (run from the repo root; needs `lake build`
# to have succeeded first so the .olean files exist)
set -euo pipefail

cd "$(dirname "$0")/../lean"

# Extract declared theorem names. All Flockzk theorems live in namespace
# FlockZk; `section` blocks (e.g. PMF) do not change the fully-qualified name.
names_file=$(mktemp -t flockzk-axiom-names-XXXXXX)
audit_file=$(mktemp -t flockzk-axioms-XXXXXX).lean
trap 'rm -f "$names_file" "$audit_file"' EXIT

grep -hE '^theorem [A-Za-z_]' Flockzk/*.lean \
  | awk '{print "FlockZk." $2}' \
  | sort -u > "$names_file"

cat >> "$names_file" <<'EOF'
VeiledFlock.ProductionFormalZK.veil_flock_statistical_zk_126
VeiledFlock.ProductionFormalZK.veil_flock_statistical_distance_lt_two_pow_neg_126
VeiledFlock.ProductionFormalZK.productionSimulator_expected_polytime
VeiledFlock.ProductionStatisticalZK.veil_flock_statistical_zk_126_of_good_coupling
VeiledFlock.ProductionStatisticalDistance.real_eq_simulated_after_coinEquiv_of_globalGood
VeiledFlock.ProductionOperationalGood.globalGood_implies_productionGood
VeiledFlock.ProductionOperationalTape.productionDecode_measure_preserving
EOF

if [ ! -s "$names_file" ]; then
  echo "lean-axioms: no theorems found — extraction broken?" >&2
  exit 1
fi

{
  echo "import Flockzk"
  echo "import VeiledFlock"
  while IFS= read -r n; do
    echo "#print axioms $n"
  done
} < "$names_file" > "$audit_file"

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

count=$(wc -l < "$names_file" | tr -d ' ')
if [ -n "$bad" ]; then
  echo "lean-axioms: FAILED — non-standard axioms found:" >&2
  echo "$bad" >&2
  exit 1
fi

echo "lean-axioms: OK — $count theorems depend only on propext / Classical.choice / Quot.sound"
