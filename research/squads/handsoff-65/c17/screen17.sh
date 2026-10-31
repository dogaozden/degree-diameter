#!/bin/sh
# usage: screen17.sh TYPE N SECS NCOMB ORDER:ID ...   (run from c17/; one heavy process at a time)
# for each group: make its table (gap, tables17.g), run mtabu17 over NCOMB random class combinations, SECS each,
# append one line per group to screen17.tsv: type, order, id, name, best cost, n, and delete the table again.
TYPE="$1"; NN="$2"; SECS="$3"; NCOMB="$4"; shift 4
mkdir -p groups17
for OI in "$@"; do
  O=${OI%%:*}; I=${OI##*:}
  F=groups17/sg_${O}_${I}.txt
  if [ ! -s "$F" ]; then
    timeout 200 nice -n 10 gap -q -c "ORDER:=$O; OUTDIR:=\"groups17\"; IDS:=[$I];" tables17.g > /dev/null 2>&1
  fi
  NAME=$(cat groups17/sg_${O}_${I}.name 2>/dev/null | tr -d '\n')
  OUT=$(TYPE="$TYPE" N="$NN" RANDCOMB="$NCOMB" SECS="$SECS" SEED=$I timeout 200 nice -n 10 ./mtabu17 "$F" 2>/dev/null | grep COMB | awk '{for(i=1;i<=NF;i++) if($i=="best") b=$(i+1); if (b>=0) print b}' | sort -n | head -1)
  printf '%s\t%s\t%s\t%s\tbest=%s\tn=%s\n' "$TYPE" "$O" "$I" "$NAME" "$OUT" "$((O*4/3))" >> screen17.tsv
  rm -f "$F"
done
