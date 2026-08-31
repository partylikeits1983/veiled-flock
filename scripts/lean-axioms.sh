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
audit_tmp=$(mktemp -t flockzk-axioms-XXXXXX)
audit_file="$audit_tmp.lean"
axioms_file=$(mktemp -t flockzk-axiom-results-XXXXXX)
mv "$audit_tmp" "$audit_file"
trap 'rm -f "$names_file" "$audit_file" "$axioms_file"' EXIT

grep -hE '^theorem [A-Za-z_]' Flockzk/*.lean \
  | awk '{print "FlockZk." $2}' \
  | sort -u > "$names_file"

cat >> "$names_file" <<'EOF'
VeiledFlock.ProductionFormalZK.veil_flock_statistical_zk_126
VeiledFlock.ProductionFormalZK.veil_flock_statistical_distance_lt_two_pow_neg_126
VeiledFlock.ProductionFormalZK.productionSimulator_expected_polytime
VeiledFlock.ProductionStatisticalZK.veil_flock_statistical_zk_126_of_good_coupling
VeiledFlock.ConcreteSecurityBound.reviewed_zkBound_lt_two_pow_neg_126
VeiledFlock.Grinding.blindAbort_lt_two_pow_neg_186
VeiledFlock.Grinding.ligeritoAbort_lt_two_pow_neg_187
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

# Lean wraps long axiom lists across output lines.  Parse complete bracketed
# records instead of grepping one line, and fail closed if any record is
# missing or unterminated.
count=$(wc -l < "$names_file" | tr -d ' ')
reported=$(printf '%s\n' "$out" \
  | grep -Ec "^'[^']+' (does not depend on any axioms|depends on axioms:)" \
  || true)
if [ "$reported" -ne "$count" ]; then
  echo "lean-axioms: FAILED — expected $count theorem reports, found $reported" >&2
  exit 1
fi

if ! printf '%s\n' "$out" | awk '
  /depends on axioms: \[/ {
    collecting = 1
    record = $0
  }
  collecting && $0 !~ /depends on axioms: \[/ {
    record = record " " $0
  }
  collecting && record ~ /\]/ {
    sub(/^.*depends on axioms: \[/, "", record)
    sub(/\].*$/, "", record)
    axiom_count = split(record, axiom, ",")
    for (i = 1; i <= axiom_count; i++) {
      gsub(/[[:space:]]/, "", axiom[i])
      if (axiom[i] != "") print axiom[i]
    }
    collecting = 0
    record = ""
  }
  END {
    if (collecting) exit 2
  }
' > "$axioms_file"; then
  echo "lean-axioms: FAILED — unterminated axiom report" >&2
  exit 1
fi

bad=$(sort -u "$axioms_file" \
  | grep -vE '^(propext|Classical\.choice|Quot\.sound)$' || true)

if [ -n "$bad" ]; then
  echo "lean-axioms: FAILED — non-standard axioms found:" >&2
  echo "$bad" >&2
  exit 1
fi

echo "lean-axioms: OK — $count theorems depend only on propext / Classical.choice / Quot.sound"
