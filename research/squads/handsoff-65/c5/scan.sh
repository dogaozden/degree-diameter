#!/bin/bash
# usage (from c5/): scan.sh TYPE SECS RANDCOMB ORDER...
# For each order: generate group tables if missing, run mcos on every non-abelian group (RANDCOMB random class
# combinations, SECS each), append "order group name type best_cost" to scan/<type>.tsv. Cost-0 edge lists kept in scan/.
T=$1; S=$2; RC=$3; shift 3
cd "$(dirname "$0")" || exit 1
TAG=$(echo "$T" | tr '|,' '_-')
OUT=scan/$TAG.tsv
for N in "$@"; do
  [ -f groups/sg_${N}_1.txt ] || timeout 900 nice -n 10 gap -q -c "ORDER:=$N; OUTDIR:=\"groups\";" ../shared/gap_tables.g > /dev/null 2>&1
  for f in groups/sg_${N}_*.txt; do
    b=$(basename "$f" .txt)
    [ -f groups/$b.name ] || continue
    grep -q "abelian=true" groups/$b.name && continue
    [ -s "scan/$TAG.$b.log" ] && grep -q "^RESULT" "scan/$TAG.$b.log" && continue
    timeout 600 env TYPE="$T" SECS=$S SEED=1 RANDCOMB=$RC EDGES="scan/$TAG.$b.best.edges" nice -n 10 ../shared/mcos "$f" > "scan/$TAG.$b.log" 2>&1
    best=$(grep "^RESULT" "scan/$TAG.$b.log" | awk '{print $3}')
    printf '%s\t%s\t%s\t%s\t%s\n' "$N" "$b" "$(head -c 40 groups/$b.name)" "$T" "$best" >> "$OUT"
    [ "$best" = "0" ] && echo "HIT $b $T" >> "$OUT"
  done
done
echo "DONE $*" >> "$OUT"
