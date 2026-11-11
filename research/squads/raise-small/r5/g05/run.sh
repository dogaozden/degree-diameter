#!/bin/bash
# Sequential job runner for card g05. Reads jobs.txt ("N m k r seed"), resumes at next.txt, stops after ~70 s.
RS=/home/user/degree-diameter/research/frontier/raise_small
G=/home/user/degree-diameter/research/squads/raise-small/r5/g05
cd "$G" || exit 1
T0=$(date +%s)
i=$(cat next.txt 2>/dev/null || echo 1)
total=$(wc -l < jobs.txt)
while [ "$i" -le "$total" ]; do
  el=$(( $(date +%s) - T0 ))
  [ "$el" -gt 45 ] && break
  set -- $(sed -n "${i}p" jobs.txt)
  N=$1; m=$2; k=$3; r=$4; s=$5
  W="runs/${m}_${k}_${r}_s${s}"
  mkdir -p "$W"
  cd "$W"
  timeout 100 nice -n 10 python3 $RS/tools/gtab.py g.tab $m $k $r > gtab.log 2>&1
  D=14 timeout 100 nice -n 10 $RS/bin/salift_s 2 g.tab 1 $s 12 10 0.3 o.sol > salift.log 2>&1
  cost=$(head -1 o.sol.best 2>/dev/null | awk '{print $4}')
  echo "$N $m $k $r $s ${cost:-NA}" >> "$G/results.txt"
  if [ "$cost" = "0" ]; then
    timeout 60 nice -n 10 python3 $RS/tools/sol2edges.py o.sol $m $k $r out.edges > s2e.log 2>&1
    timeout 60 nice -n 10 $RS/bin/apsp out.edges 3 14 > apsp.log 2>&1
    echo "COST0 $N $m $k $r $s apsp: $(grep RESULT apsp.log)" >> "$G/results.txt"
  fi
  rm -f g.tab out.edges
  cd "$G"
  i=$((i+1))
  echo "$i" > next.txt
done
echo "next=$(cat next.txt) of $total"
tail -n 3 results.txt
