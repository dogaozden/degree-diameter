#!/bin/bash
# evo.sh start.in prefix gens: each generation runs 4 cold po7 anneals (T0 0.3/0.5/0.7/0.9 -> 0.04, SECS each) from the
# current best and keeps the lowest; when the best is <= 20, two wpo runs (LMAX 3000 DECAY 10); stops at cost 0.
cd /tmp/claude-0/-home-user-degree-diameter/468680c1-3e6e-599d-b1ca-881241eddc40/scratchpad/w
cur=$1; P=$2; G=${3:-20}; S=${SECS:-400}
cost() { SCORE=1 /tmp/po7 $1 | tail -1 | grep -oE "cost=[0-9]+" | cut -d= -f2; }
cp $cur $P.best.in; b=$(cost $P.best.in); echo "gen 0 best $b $(date +%T)"
for g in $(seq 1 $G); do
  if [ "$b" -le 20 ]; then
    for k in 1 2; do LMAX=3000 DECAY=10 SECS=600 SEED=$g$k OUT=$P.w$k.in OUT0=$P.w$k.0.in nice /tmp/wpo $P.best.in > $P.w$k.log 2>&1 & done; wait
    for k in 1 2; do [ -f $P.w$k.0.in ] && { cp $P.w$k.0.in $P.struct0.in; echo "STRUCT0 $P.struct0.in $(date +%T)"; exit 0; }; done
  fi
  i=0; for t0 in ${TS:-0.3 0.5 0.7 0.9}; do i=$((i+1)); SECS=$S SEED=$g$i$RANDOM T0=$t0 T1=0.04 PF=0.3 PH=0.7 OUT=$P.g$i.in OUT0=$P.g$i.0.in nice /tmp/po7 $P.best.in > $P.g$i.log 2>&1 & done; wait
  for i in 1 2 3 4; do [ -f $P.g$i.0.in ] && { cp $P.g$i.0.in $P.struct0.in; echo "STRUCT0 $P.struct0.in"; exit 0; }; done
  for i in 1 2 3 4; do c=$(cost $P.g$i.in); if [ "$c" -lt "$b" ]; then b=$c; cp $P.g$i.in $P.best.in; fi; echo -n "$c "; done
  echo " -> gen $g best $b $(date +%T)"
done
