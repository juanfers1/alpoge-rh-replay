#!/usr/bin/env bash
# Compare the public statements of the replay with propositions elaborated from Mathlib alone.
#
# Run through `lake env` from the replay's `lean/` directory, so that LEAN_PATH reaches Mathlib and
# the project's build outputs:
#
#   lake build +Main:olean
#   lake env bash /path/to/audit/statement-check.sh main /path/to/empty/output-dir
#
#   lake build Statements          # quick check of the statement definitions only
#   lake env bash /path/to/audit/statement-check.sh statements /path/to/empty/output-dir
#
# The output directory receives the compiled StatementCheck and ExpectedStatements modules. Lean
# exits with a non-zero status if any comparison or axiom check reports an error.
set -euo pipefail
mode="${1:?usage: statement-check.sh main|statements OUTPUT_DIR}"
out="${2:?usage: statement-check.sh main|statements OUTPUT_DIR}"
here="$(cd "$(dirname "$0")" && pwd -P)"
: "${LEAN_PATH:?run this script through lake env}"
case "$mode" in
  main) target="$here/CompareMain.lean" ;;
  statements) target="$here/CompareStatements.lean" ;;
  *) echo "unknown mode: $mode" >&2; exit 2 ;;
esac
mkdir -p "$out"
out="$(cd "$out" && pwd -P)"
lean --version
# The checker imports only Lean; the expected statements import only Mathlib.
lean -R "$here" -o "$out/StatementCheck.olean" "$here/StatementCheck.lean"
lean -R "$here" -o "$out/ExpectedStatements.olean" "$here/ExpectedStatements.lean"
LEAN_PATH="$out:$LEAN_PATH" lean "$target"
