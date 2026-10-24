#!/bin/bash
# Card c2 driver: ORBIT="3 2 2", d=8, D=10, 150 s per seed, up to 5 seeds per group.
B=/tmp/claude-0/-home-user-degree-diameter/2744c2da-0db8-5a6f-87c3-01a128c9c95e/scratchpad/bin
C=/home/user/degree-diameter/research/squads/r5/c2
SUM=$C/summary.txt
cd /home/user/degree-diameter/research/squads || exit 1
ORBW_ON=0
CARDGROUPS=(
"g1_psl3_sl11_247|prod psl 3 sl 11 247"
"g2_psl7_psl7_139|prod psl 7 psl 7 139"
"g3_sl5_sl32_1|prod sl 5 sl 32 1"
"g4_sl8_psl25_1|prod sl 8 psl 25 1"
"g5_psl3_sl17_67|prod psl 3 sl 17 67"
)
echo "start $(date +%T)" >> $SUM
for g in "${CARDGROUPS[@]}"; do
  tag=${g%%|*}; grp=${g#*|}
  for seed in 1 2 3 4 5; do
    W=""; [ "$ORBW_ON" = 1 ] && W="ORBW=3"
    log=$C/${tag}_s${seed}.log; out=$C/${tag}_s${seed}.txt
    start=$(date +%s)
    env ORBIT="3 2 2" $W timeout 250 nice -n 10 $B/haar_sym 8 10 150 $seed 8 $out $grp > $log 2>&1
    el=$(( $(date +%s) - start ))
    best=$(grep -o 'best=[0-9]*' $log | tail -1 | cut -d= -f2)
    [ -z "$best" ] && best=NORESULT
    chk=$(grep -c 'full diameter check: OK' $log)
    solved=no; [ "$best" = 0 ] && solved=YES
    echo "$tag seed=$seed orbw=${W:-0} best=$best solved=$solved check_ok=$chk elapsed=${el}s" >> $SUM
    if [ "$best" = NORESULT ] && [ "$el" -lt 20 ]; then echo "ABORT: early failure, see $log" >> $SUM; exit 1; fi
    if [ "$solved" = YES ]; then break; fi
    if [ "$best" = 1 ] || [ "$best" = 2 ]; then ORBW_ON=1; fi
  done
done
echo "done $(date +%T)" >> $SUM
