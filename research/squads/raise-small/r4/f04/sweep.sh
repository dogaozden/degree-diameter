#!/bin/bash
# usage: sweep.sh ORDERFILE LINE FIRSTSEED -- starts a run only if elapsed < 55 s; prints NEXT line,seed to resume
RS=/home/user/degree-diameter/research/frontier/raise_small
F=/home/user/degree-diameter/research/squads/raise-small/r4/f04
cd $F
T=$(date +%s)
first=$3
tail -n +$2 $1 | while read N m k r d fpf; do
  for seed in 11 12; do
    if [ "$seed" -lt "$first" ]; then continue; fi
    if [ $(( $(date +%s) - T )) -ge 55 ]; then echo "RESUME_AT line-group $N $m $k $r seed $seed"; exit 0; fi
    [ -f g_${m}_${k}_${r}.tab ] || python3 $RS/tools/gtab.py g_${m}_${k}_${r}.tab $m $k $r >/dev/null 2>&1
    out=$(D=14 timeout 100 nice -n 10 $RS/bin/salift_s 2 g_${m}_${k}_${r}.tab 1 $seed 13 10 0.3 s_${m}_${k}_${r}_${seed}.sol 2>&1)
    cost=$(echo "$out" | grep '^end best' | awk '{print $3}')
    echo "$N $m $k $r $seed ${cost:-NA}" >> results.txt
    if [ -f s_${m}_${k}_${r}_${seed}.sol ]; then echo "COST0 $N $m $k $r $seed" >> results.txt; fi
    if [ "${cost:-99}" -gt 6 ]; then rm -f s_${m}_${k}_${r}_${seed}.sol.best; fi
  done
  rm -f g_${m}_${k}_${r}.tab
  first=11
done
echo DONE_ALL
