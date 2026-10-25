#!/bin/bash
# Encode, solve with kissat (binary DRAT proof), check the proof with drat-trim, log hashes and results.
# usage: certify.sh k "encoder options" outdir     (needs KISSAT and DRATTRIM env vars or defaults below)
# Solvers: kissat (github.com/arminbiere/kissat, master of 2026-10-25), drat-trim (github.com/marijnheule/drat-trim).
set -e
k=$1; opts=$2; out=$3
KISSAT=${KISSAT:-kissat}; DRATTRIM=${DRATTRIM:-drat-trim}
here=$(cd "$(dirname "$0")" && pwd)
tag="k${k}$(echo $opts | tr -d ' -')"
mkdir -p "$out"
python3 "$here/enc_quot.py" $k "$out/$tag.cnf" $opts > "$out/$tag.log"
echo "cnf sha256 $(sha256sum "$out/$tag.cnf" | cut -d' ' -f1)" >> "$out/$tag.log"
start=$(date +%s.%N)
set +e
"$KISSAT" -q "$out/$tag.cnf" "$out/$tag.drat" > "$out/$tag.solve" 2>&1
rc=$?
set -e
end=$(date +%s.%N)
echo "kissat exit $rc ($(grep '^s ' "$out/$tag.solve")) time $(echo "$end - $start" | bc) s" >> "$out/$tag.log"
if [ $rc -eq 20 ]; then
  echo "drat sha256 $(sha256sum "$out/$tag.drat" | cut -d' ' -f1) size $(stat -c %s "$out/$tag.drat")" >> "$out/$tag.log"
  start=$(date +%s.%N)
  "$DRATTRIM" "$out/$tag.cnf" "$out/$tag.drat" -t 200000 > "$out/$tag.check" 2>&1 || true
  end=$(date +%s.%N)
  echo "drat-trim: $(grep -o -E '(NOT )?VERIFIED' "$out/$tag.check" | head -1) time $(echo "$end - $start" | bc) s" >> "$out/$tag.log"
fi
cat "$out/$tag.log"
