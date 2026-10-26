#!/bin/bash
# k6 (3,10): p=7 joint base+voltage annealing (salift_s2, D=10) over all groups of orders 58..63 (n = 14N = 812..882).
# Phase 1: screen every group, 20 CPU s each, seed 1, ascending N (non-abelian first inside each order).
#          Any cost-0 state is converted with best2edges.py and checked with score48 at once.
# Phase 2: push the 2 best non-zero states (lowest cost, then largest N) with START restarts, seeds 2..4, 100 s each.
T=/home/user/degree-diameter/research/squads/own-small/tools
GT=/home/user/degree-diameter/research/squads/own-small/runs/gtxt
K=/home/user/degree-diameter/research/squads/own-small/r2/k6
P=7
export D=10
cd $K || exit 1
mkdir -p runs
RES=$K/results.tsv
CHK=$K/checks.log
touch $RES $CHK

cost_of() { local c; c=$(grep '^end best' "$1" 2>/dev/null | tail -1 | awk '{print $3}'); echo "${c:-99}"; }

check() { # N base: if base.sol exists (cost 0), convert and score
  local N=$1 base=$2
  [ -f "$base.sol" ] || return 0
  python3 -I $T/best2edges.py $GT/g$N.txt $base.sol $base.edges > $base.conv.txt 2>&1
  $T/bin/score48 $base.edges 3 10 > $base.check.txt 2>&1
  echo "CHECK N=$N base=$base : $(tail -1 $base.check.txt)" >> $CHK
}

LASTC=99
run() { # N id seed secs base [start.best]
  local N=$1 id=$2 seed=$3 secs=$4 base=$5 st=$6
  if [ -n "$st" ]; then export START="$st"; else unset START; fi
  $T/bin/salift_s2 $P $GT/g$N.txt $id $seed $secs 10 0.3 $base.sol > $base.log 2>&1
  unset START
  LASTC=$(cost_of $base.log)
  printf "%s\t%s\t%s\t%s\t%s\t%s\n" $N $id $seed $secs $LASTC $base >> $RES
  echo "[$(date -u +%H:%M:%S)] N=$N id=$id seed=$seed secs=$secs cost=$LASTC" >> $K/progress.log
  if [ "$LASTC" = "0" ]; then check $N $base; fi
}

# Phase 1: screen
ORDER="58:1 58:2 59:1 60:1 60:2 60:3 60:5 60:6 60:7 60:8 60:9 60:10 60:11 60:12 60:4 60:13 61:1 62:1 62:2 63:1 63:3 63:2 63:4"
for pair in $ORDER; do
  N=${pair%%:*}; id=${pair##*:}
  run $N $id 1 20 runs/N${N}_g${id}_s1
done

# Phase 2: push. Candidates: cost >= 1, lowest cost first, then largest N.
awk -F'\t' '$5>=1 && $5<99 {print $5, $1, $2, $6}' $RES | sort -k1,1n -k2,2nr > $K/cands.txt
read C1 N1 I1 B1 < <(sed -n 1p $K/cands.txt)
read C2 N2 I2 B2 < <(sed -n 2p $K/cands.txt)
if [ -n "$B1" ]; then
  run $N1 $I1 2 100 ${B1}_r2 ${B1}.sol.best; X1=$LASTC; B1r=${B1}_r2
fi
if [ -n "$B2" ]; then
  run $N2 $I2 2 100 ${B2}_r2 ${B2}.sol.best; X2=$LASTC; B2r=${B2}_r2
fi
# continue the better chain with fresh seeds
if [ -n "$B1" ] && { [ -z "$B2" ] || [ "$X1" -le "$X2" ]; }; then
  BN=$N1; BI=$I1; BB=$B1r
else
  BN=$N2; BI=$I2; BB=$B2r
fi
run $BN $BI 3 100 ${BB}_r3 ${BB}.sol.best
run $BN $BI 4 100 ${BB}_r4 ${BB}_r3.sol.best
echo DONE >> $K/progress.log
