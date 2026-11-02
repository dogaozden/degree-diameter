#!/bin/bash
# pool.sh D p MINN MAXCOST SECS LINKS OUTDIR DIR...: chain every salift_s state "g<N>_<m>_<k>_<r>_D<D>_p<p>_*.sol.best"
# found in DIR... with N >= MINN and cost <= MAXCOST (ascending cost, then descending N), LINKS links of SECS CPU-s
# each at T0 = 4 (chain.sh). Stops at the first state that reaches cost 0 (chain.sh checks it with apsp).
H=$(cd "$(dirname "$0")/.." && pwd); D=$1; p=$2; MINN=$3; MC=$4; S=$5; L=$6; O=$7; shift 7
mkdir -p "$O"
for f in $(for d in "$@"; do ls "$d"/g*_D${D}_p${p}_*.sol.best 2>/dev/null; done); do
  read N id pp c < <(head -1 "$f"); b=$(basename "$f"); IFS=_ read g m k r rest <<< "${b#g}"
  [ "$N" -ge "$MINN" ] && [ "$c" -le "$MC" ] && echo "$c $N $m $k $r $f"
done | sort -k1n -k2nr | while read c N m k r f; do
  echo "== $f cost $c" >> "$O/pool.log"
  "$H/tools/chain.sh" $D $p $m $k $r "$f" $S $L $((RANDOM + 5000)) "$O/c${N}_${m}_${k}_${r}" 4 0.3 >> "$O/pool.log" 2>&1
  grep -q "RESULT VALID" "$O/pool.log" && break
done
