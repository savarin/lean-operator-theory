#!/bin/bash
# Negative control: confirm the comparator rejects a mutated theorem statement.
#
# Mutates vonNeumann_inequality's bound in CrouzeixPalenciaChallenge.lean,
# doubling the right-hand side (polynomialSupNorm p ... -> 2 * polynomialSupNorm
# p ...). The Solution still proves the original (unmutated) bound via the
# library, so the mutated Challenge and the Solution should no longer match.
# Temporarily overwrites the Challenge for the mutated build, then restores it.
# Requires a passing baseline first.
set -euo pipefail
cd "$(dirname "$0")/.."

: "${COMPARATOR:?Set COMPARATOR to the comparator binary path}"
: "${LEAN4EXPORT:?Set LEAN4EXPORT to a v4.33.0-compatible lean4export binary}"

if [[ -n "${FAKE_LANDRUN:-}" ]]; then
  export COMPARATOR_LANDRUN="$FAKE_LANDRUN"
fi

CONFIG="comparator-crouzeix-palencia.json"
CHALLENGE="CrouzeixPalenciaChallenge.lean"

echo "=== Negative control ==="

# Step 1: Verify baseline passes
echo "[1/3] Verifying baseline ..."
BASELINE=$(COMPARATOR_LEAN4EXPORT="$LEAN4EXPORT" lake env "$COMPARATOR" "$CONFIG" 2>&1 || true)
if ! echo "$BASELINE" | grep -qi "Your solution is okay"; then
  echo "FAIL: baseline comparator run does not pass — negative control is unreliable"
  echo "$BASELINE" | tail -5
  exit 1
fi
echo "  Baseline passes"

# Step 2: Build a mutated Challenge in a temp directory
echo "[2/3] Building mutated Challenge ..."
WORKDIR=$(mktemp -d "${TMPDIR:-/tmp}/neg-ctrl-XXXXXX")

# Save original before any mutation
cp "$CHALLENGE" "$WORKDIR/Challenge.lean.orig"
trap 'cp "$WORKDIR/Challenge.lean.orig" "$CHALLENGE"; rm -rf "$WORKDIR"' EXIT

# Mutate: double the right-hand side of vonNeumann_inequality
sed 's/      polynomialSupNorm p (Metric.closedBall (0 : ℂ) 1) := by/      2 * polynomialSupNorm p (Metric.closedBall (0 : ℂ) 1) := by/' \
  "$CHALLENGE" > "$WORKDIR/Challenge.lean"

cp "$WORKDIR/Challenge.lean" "$CHALLENGE"

echo "  Mutated: doubled the RHS of vonNeumann_inequality"
if ! lake build CrouzeixPalenciaChallenge 2>&1 | tail -3; then
  echo "  (mutated build failed — trap restores $CHALLENGE)"
  exit 1
fi

# Step 3: Run comparator on mutated Challenge
echo "[3/3] Running comparator on mutated Challenge ..."
OUTPUT=$(COMPARATOR_LEAN4EXPORT="$LEAN4EXPORT" lake env "$COMPARATOR" "$CONFIG" 2>&1 || true)
echo "$OUTPUT" | tail -5

# Trap restores Challenge.lean on exit; rebuild to reset .lake cache
echo "  Restoring original and rebuilding ..."

if echo "$OUTPUT" | grep -q "^FAIL PalomarCrouzeixPalencia.vonNeumann_inequality"; then
  echo "PASS: comparator correctly rejected the mutated Challenge (statement mismatch)"
  exit 0
else
  echo "FAIL: comparator did not reject vonNeumann_inequality as expected"
  exit 1
fi
