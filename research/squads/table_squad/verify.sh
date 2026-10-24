#!/bin/bash
# Independent check of a haar_gen3-format solution file: build_haar2.py rebuilds the Haar graph from the group
# definition (two BFS, degrees, repeated edges) and writes the edge list; apsp.c then runs an all-pairs BFS on that
# edge list with no symmetry assumed. Usage: verify.sh SOL.txt OUT.check.txt   (apsp binary: $APSP)
set -e
SOL=$1; OUT=$2; HERE=$(cd "$(dirname "$0")" && pwd); ROOT=$(cd "$HERE/../../.." && pwd)
APSP=${APSP:-$ROOT/research/lifts/coordinator_check/apsp}
read d D rest < <(head -1 "$SOL")
EDG=$(mktemp)
{ echo "== solution file $SOL (sha256 $(sha256sum "$SOL" | cut -c1-64))"; cat "$SOL"
  echo "== build_haar2.py"; python3 "$ROOT/research/frontier/build_haar2.py" "$SOL" "$EDG"
  echo "== apsp.c all-pairs on the edge list (sha256 $(sha256sum "$EDG" | cut -c1-64))"; "$APSP" "$EDG" "$d" "$D"; } > "$OUT" 2>&1 || true
rm -f "$EDG"; grep -E "^VALID|^INVALID|RESULT" "$OUT"
