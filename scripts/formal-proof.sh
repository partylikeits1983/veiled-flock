#!/usr/bin/env bash
# Build the Lean formalization with concise progress, then reject any theorem
# that depends on axioms outside Lean's standard trusted set.
set -euo pipefail

repo_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)
lake_bin=${LAKE:-lake}
bar_width=${FORMAL_PROOF_BAR_WIDTH:-36}

if ! [[ $bar_width =~ ^[1-9][0-9]*$ ]]; then
  echo "formal-proof: FORMAL_PROOF_BAR_WIDTH must be a positive integer" >&2
  exit 2
fi

interactive=false
if [[ -t 2 ]]; then
  interactive=true
fi

draw_progress() {
  local completed=$1
  local total=$2
  local percent filled empty filled_bar empty_bar

  percent=$((completed * 100 / total))
  filled=$((completed * bar_width / total))
  empty=$((bar_width - filled))
  printf -v filled_bar '%*s' "$filled" ''
  printf -v empty_bar '%*s' "$empty" ''
  filled_bar=${filled_bar// /#}
  empty_bar=${empty_bar// /-}
  printf '\r\033[2KLean build [%s%s] %3d%% (%d/%d)' \
    "$filled_bar" "$empty_bar" "$percent" "$completed" "$total" >&2
}

cd "$repo_root/lean"

echo "formal-proof: preparing the pinned Mathlib cache" >&2
"$lake_bin" exe cache get

echo "formal-proof: building the VeiledFlock Lean proofs" >&2
if $interactive; then
  draw_progress 0 1
else
  echo "Lean build [  0%] 0/? targets" >&2
fi
set +e
"$lake_bin" build VeiledFlock 2>&1 | {
  next_report=0
  saw_progress=$interactive
  completed=0
  total=1

  while IFS= read -r line; do
    if [[ $line =~ \[([0-9]+)/([0-9]+)\][[:space:]]+Built ]]; then
      completed=${BASH_REMATCH[1]}
      total=${BASH_REMATCH[2]}
      saw_progress=true
      percent=$((completed * 100 / total))

      if $interactive; then
        draw_progress "$completed" "$total"
      elif ((percent >= next_report)); then
        printf 'Lean build [%3d%%] %d/%d targets\n' \
          "$percent" "$completed" "$total" >&2
        next_report=$(((percent / 5 + 1) * 5))
      fi
    else
      if $interactive && $saw_progress; then
        printf '\r\033[2K' >&2
      fi
      printf '%s\n' "$line" >&2
      if $interactive && $saw_progress; then
        draw_progress "$completed" "$total"
      fi
    fi
  done

  if $interactive && $saw_progress; then
    printf '\n' >&2
  fi
}
build_status=${PIPESTATUS[0]}
set -e

if ((build_status != 0)); then
  if $interactive; then
    printf '\r\033[2K' >&2
  fi
  echo "formal-proof: Lean build failed" >&2
  exit "$build_status"
fi

if $interactive; then
  printf '\r\033[2KLean build [' >&2
  printf '%*s' "$bar_width" '' | tr ' ' '#' >&2
  printf '] 100%% (complete)\n' >&2
else
  echo "Lean build [100%] complete" >&2
fi

echo "formal-proof: auditing theorem axioms" >&2
cd "$repo_root"
scripts/lean-axioms.sh
echo "formal-proof: verified" >&2
