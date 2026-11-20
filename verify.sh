#!/usr/bin/env bash
set -euo pipefail
record="$(cd "$(dirname "$0")" && pwd -P)"
work="${1:?Supply an empty directory path on a large Linux build volume}"
if ! command -v elan >/dev/null; then
  echo "Install elan and make it available on PATH before starting the replay." >&2
  exit 1
fi
mkdir -p "$work"
work="$(cd "$work" && pwd -P)"
if [[ -n "$(ls -A "$work")" ]]; then
  echo "Choose an empty directory for this independent replay." >&2
  exit 1
fi
exec > >(tee "$work/replay.log") 2>&1
export ELAN_HOME="$work/elan"
export XDG_CACHE_HOME="$work/cache"
mkdir "$work/parts"
cd "$work/parts"
while read -r hash part; do
  curl --fail --location --retry 4 --output "$part" "https://alpo.ge/lean.tar.gz.$part"
done < "$record/parts.sha256"
sha256sum -c "$record/parts.sha256"
cat part* | tar -xz --no-same-owner -C "$work"
cd "$work/lean"
toolchain="$(cat lean-toolchain)"
test "$toolchain" = "leanprover/lean4:v4.33.1"
elan toolchain install "$toolchain"
elan run "$toolchain" lean --version
lake_cmd=(elan run "$toolchain" lake)
"${lake_cmd[@]}" exe cache get
test "$(git -C .lake/packages/mathlib rev-parse HEAD)" = "0df444a360eaa60ab8c11dca51a86af692955474"
if [[ "${2:-}" == "--prepare-only" ]]; then echo "Prepared project in $work/lean"; exit 0; fi
"${lake_cmd[@]}" build +Main:olean
echo REPLAY_SOURCE_BUILD_PASSED
"${lake_cmd[@]}" env lean "$record/Audit.lean"
echo REPLAY_AXIOM_AUDIT_PASSED
"${lake_cmd[@]}" env bash "$record/audit/statement-check.sh" main "$work/statement-check"
echo REPLAY_STATEMENT_CHECK_PASSED
"${lake_cmd[@]}" env leanchecker --fresh Main
echo REPLAY_FRESH_KERNEL_PASSED
