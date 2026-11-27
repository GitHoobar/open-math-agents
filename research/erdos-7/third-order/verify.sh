#!/usr/bin/env bash
set -euo pipefail

if [[ $# != 1 ]]; then
  echo "Usage: bash verify.sh /path/to/formal-conjectures" >&2
  exit 2
fi
source_dir="$(cd "$(dirname "$0")" && pwd)"
checkout="$(cd "$1" && pwd)"
objects="$(mktemp -d)"
trap 'rm -rf -- "$objects"' EXIT
cd "$checkout"
lake env bash -eu -c '
  export LEAN_PATH="$2${LEAN_PATH:+:$LEAN_PATH}"
  for module in ThirdOrderBounds ThirdOrderTail ThirdOrderDeletion ThirdOrderAvoidance ThirdOrderCRT \
                ThirdOrderAllocation ThirdOrderProducts ThirdOrderUnlabel ThirdOrderMain; do
    lean --root="$1" -o "$2/$module.olean" "$1/$module.lean"
  done
  lean --root="$1" "$1/Audit.lean"
' _ "$source_dir" "$objects"
