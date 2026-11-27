#!/usr/bin/env bash
set -euo pipefail

source_dir="$(cd "$(dirname "$0")" && pwd)"
if [[ $# != 1 ]]; then
  echo "Usage: bash verify.sh /path/to/formal-conjectures" >&2
  exit 2
fi
checkout="$(cd "$1" && pwd)"
cd "$checkout"
lake build 'FormalConjectures.ErdosProblems.«7»'

obj_dir="$(mktemp -d)"
trap 'rm -rf -- "$obj_dir"' EXIT
lake env bash -eu -c '
  export LEAN_PATH="$2${LEAN_PATH:+:$LEAN_PATH}"
  for module in PrimeExtension OddReduction OddLift SlopeObstruction SharpRepair PrimeReplacement DepthBound MultiplicityLift; do
    lean --root="$1" -o "$2/$module.olean" "$1/$module.lean"
  done
  lean --root="$1" "$1/Verify.lean"
' _ "$source_dir" "$obj_dir"
