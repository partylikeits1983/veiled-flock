#!/bin/bash
# Verify the ASCII architecture diagrams under docs/architecture/.
#
# Six invariants:
#   1. files   — the five canonical documents exist                        (FAIL if not)
#   2. mirror  — .claude/architecture/ matches docs/architecture/ byte for byte
#                (SKIP when absent: the mirror is machine-local and untracked;
#                 FAIL when it exists and differs)
#   3. width   — no line exceeds 100 columns, so diagram lanes never wrap
#   4. fences  — every fenced block in a diagram file is tagged, diagrams use text,
#                and text blocks hold printable ASCII only (prose may use UTF-8)
#   5. links   — every relative markdown link resolves to an existing file
#   6. anchors — every path.rs:LINE anchor is repo-root-relative, names a real file,
#                and points at a line the file actually has
#
# Deliberately NOT checked, because no cheap textual rule gets them right: that a
# canonical file contains any diagram at all, that the diagram count matches the plan,
# and that an anchored line still holds the symbol it names. Those stay human checks.
#
# Usage: scripts/check-diagrams.sh   (run from anywhere; cds to the repo root)
set -euo pipefail

cd "$(dirname "$0")/.."

CANON=docs/architecture
MIRROR=.claude/architecture
FENCE='```'
status=0

fail() { echo "[check-diagrams.sh] FAIL: $*" >&2; status=1; }
pass() { echo "[check-diagrams.sh] PASS: $*"; }
skip() { echo "[check-diagrams.sh] SKIP: $*"; }

# --- 1. required files ----------------------------------------------------
required=(
  "$CANON/README.md"
  "$CANON/flock-core-sequence.md"
  "$CANON/veil-f128-sequence.md"
  "$CANON/flock-prover-sequence.md"
  "$CANON/class-diagram.md"
)
missing=0
for f in "${required[@]}"; do
  if [ ! -f "$f" ]; then
    fail "missing required file: $f"
    missing=1
  fi
done
if [ "$missing" -eq 0 ]; then pass "all five canonical documents present"; fi

# --- 2. mirror (machine-local; absence is not a failure) ------------------
if [ ! -d "$MIRROR" ]; then
  skip "mirror absent at $MIRROR (machine-local and untracked; regenerate with"\
       "mkdir -p $MIRROR && cp $CANON/*.md $MIRROR/)"
elif ! diff_out=$(diff -r "$CANON" "$MIRROR" 2>&1); then
  fail "mirror drifted from canonical (regenerate with cp, never hand-edit):"
  printf '%s\n' "$diff_out" >&2
else
  pass "mirror byte-identical to canonical"
fi

# --- 3. width -------------------------------------------------------------
long=$(awk 'length > 100 { print FILENAME ":" FNR ": " length " columns" }' "$CANON"/*.md)
if [ -n "$long" ]; then
  fail "lines exceed 100 columns:"
  printf '%s\n' "$long" >&2
else
  pass "every line at or under 100 columns"
fi

# --- 4. fences and ASCII --------------------------------------------------
# A bare or mistagged fence would let a diagram escape the ASCII check, so the
# tag itself is verified. README.md may also use markdown and sh blocks.
fence_bad=$(LC_ALL=C awk -v fence="$FENCE" '
  index($0, fence) == 1 {
    if (inblock) { inblock = 0; next }
    tag = substr($0, length(fence) + 1)
    base = FILENAME; sub(/.*\//, "", base)
    if (tag == "text") { inblock = 1; next }
    if (base == "README.md" && (tag == "markdown" || tag == "sh")) { inblock = 1; next }
    print FILENAME ":" FNR ": fence tag is not allowed here: " tag
    inblock = 1
  }
' "$CANON"/*.md)
nonascii=$(LC_ALL=C awk -v fence="$FENCE" '
  index($0, fence) == 1 && !inblock { inblock = (substr($0, length(fence)+1) == "text"); next }
  index($0, fence) == 1 &&  inblock { inblock = 0; next }
  inblock {
    line = $0
    gsub(/\t/, " ", line)
    if (line ~ /[^ -~]/) print FILENAME ":" FNR ": non-ASCII byte inside a text block"
  }
' "$CANON"/*.md)
if [ -n "$fence_bad$nonascii" ]; then
  fail "fenced-block violations:"
  if [ -n "$fence_bad" ]; then printf '%s\n' "$fence_bad" >&2; fi
  if [ -n "$nonascii" ]; then printf '%s\n' "$nonascii" >&2; fi
else
  pass "fences tagged correctly and all text blocks are pure ASCII"
fi

# --- 5. relative links ----------------------------------------------------
check_links() {
  local file=$1 dir target
  dir=$(dirname "$file")
  # A file with no links makes grep exit 1; under set -e that would abort the run.
  { grep -oE '\]\([^)]+\)' "$file" || true; } | sed -E 's/^\]\(//; s/\)$//' \
    | while read -r target; do
    case "$target" in
      http*|mailto:*|'#'*) continue ;;
    esac
    target=${target%%#*}
    [ -n "$target" ] || continue
    [ -e "$dir/$target" ] || echo "broken link in $file -> $target"
  done
}
broken=$(check_links docs/ARCHITECTURE.md
         for f in "$CANON"/*.md; do check_links "$f"; done)
if [ -n "$broken" ]; then
  fail "unresolved relative links:"
  printf '%s\n' "$broken" >&2
else
  pass "every relative link resolves"
fi

# --- 6. anchors -----------------------------------------------------------
# Sweep every file.rs:LINE token, not only the well-formed ones: an anchor that
# is not repo-root-relative must fail loudly rather than pass unseen.
anchor_bad=$({ grep -ohE '[A-Za-z0-9_./-]+\.rs:[0-9]+' "$CANON"/*.md || true; } | sort -u \
  | while IFS=: read -r path line; do
      # Leading '(' on each pattern is required: inside $( ), bash reads a bare
      # 'pattern)' as closing the command substitution.
      case "$path" in
        (crates/*|scripts/*|docs/*|lean/*) ;;
        (*) echo "anchor is not repo-root-relative: $path:$line"; continue ;;
      esac
      if [ ! -f "$path" ]; then
        echo "anchor path does not exist: $path:$line"
      elif [ "$(wc -l < "$path")" -lt "$line" ]; then
        echo "anchor past end of file: $path:$line"
      fi
    done)
if [ -n "$anchor_bad" ]; then
  fail "bad file:line anchors:"
  printf '%s\n' "$anchor_bad" >&2
else
  pass "every file:line anchor is repo-root-relative and resolves"
fi

if [ "$status" -ne 0 ]; then
  echo "[check-diagrams.sh] FAIL: diagram invariants violated" >&2
  exit 1
fi
echo "[check-diagrams.sh] PASS: all diagram invariants hold"
