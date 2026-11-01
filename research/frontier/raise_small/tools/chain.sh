#!/bin/bash
# chain.sh D p m k r START.best SECS LINKS SEED0 OUTDIR [T0 T1]: continue a salift_s state over Z_m x|_r Z_k with
# LINKS restarts of SECS seconds (seeds SEED0, SEED0+1, ...), each from the best state so far. Stops at cost 0, then
# rebuilds the lift (sol2edges.py) and checks it all-pairs (apsp) at D and D-1. Log: OUTDIR/chain.log.
H=$(cd "$(dirname "$0")/.." && pwd); D=$1; p=$2; m=$3; k=$4; r=$5; ST=$6; S=$7; L=$8; s0=$9; O=${10}; T0=${11:-10}; T1=${12:-0.3}
mkdir -p "$O"; N=$((m * k)); tag=g${N}_${m}_${k}_${r}; tab=$O/$tag.tab
[ -f "$tab" ] || python3 "$H/tools/gtab.py" "$tab" $m $k $r 2>/dev/null
cur=$O/${tag}_D${D}_p${p}_chain.sol; [ -f "$cur.best" ] || cp "$ST" "$cur.best"   # resume an existing chain
for i in $(seq 0 $((L - 1))); do
  s=$((s0 + i))
  res=$(START="$cur.best" D=$D timeout $((4 * S + 120)) nice -n 5 "$H/bin/salift_s" $p "$tab" 1 $s $S $T0 $T1 "$cur" | tail -1)
  if [ -f "$cur" ]; then best=0; else best=$(head -1 "$cur.best" | awk '{print $4}'); fi; echo "link $i seed $s N=$N n=$((2*p*N)) best=$best" | tee -a "$O/chain.log"
  if [ "$best" = "0" ]; then
    python3 "$H/tools/sol2edges.py" "$cur" $m $k $r "${cur%.sol}.edges" > /dev/null
    echo "$("$H/bin/apsp" "${cur%.sol}.edges" 3 $D | tail -1) | at D-1: $("$H/bin/apsp" "${cur%.sol}.edges" 3 $((D - 1)) | tail -1)" | tee -a "$O/chain.log"
    break
  fi
done
rm -f "$tab"
