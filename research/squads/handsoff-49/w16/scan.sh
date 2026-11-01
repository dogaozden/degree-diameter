#!/bin/bash
# scan.sh BASE GROUPLIST SECS SEED OUTTSV FROM TO : tabu (flift + TABU=1) of BASE over each group in lines FROM..TO
cd "$(dirname "$0")"
BASE=$1; LIST=$2; SECS=$3; SEED=$4; OUT=$5; FROM=$6; TO=$7
mkdir -p scanout
sed -n "${FROM},${TO}p" "$LIST" | while read N SPEC; do
  tag=$(echo "$SPEC" | tr ':' '_')
  line=$(TABU=1 timeout $((SECS*3+60)) nice -n 10 ./tabu "$BASE" "$SPEC" 4 9 "$SECS" "$SEED" 8 "scanout/$(basename $BASE .base)_$tag" 2>/dev/null | grep '^RESULT' | tail -1)
  best=$(echo "$line" | sed -n 's/.*best=\([0-9-]*\).*/\1/p')
  ev=$(echo "$line" | sed -n 's/.*evals=\([0-9]*\).*/\1/p')
  printf "%s\t%s\t%s\t%s\n" "$N" "$SPEC" "${best:-fail}" "${ev:-0}" | tee -a "$OUT"
done
