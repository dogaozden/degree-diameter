#!/bin/bash
# run_exh.sh BUDGET_CPU_S : exhaustive Delta=5 Haar search (haar5 exhp) over ranked non-abelian groups of order 216
T=/home/user/degree-diameter/research/squads/hunt-d5/tools
W=/home/user/degree-diameter/research/squads/hunt-d5/r3/a1
used=0.0
TIMEFORMAT='%U %S'
while read i gp zc; do
  # stop when the CPU budget is spent
  if awk -v u=$used -v b=$1 'BEGIN{exit !(u>=b)}'; then echo "BUDGET_STOP used=$used" >> $W/exh216.log; break; fi
  f=$W/tables/g216_$i.bin
  t=$( { time nice -n 10 python3 $T/gapgroup.py table 216 $i $f; } 2>&1 >/dev/null | tail -n 1 )
  t2=$( { time timeout 150 nice -n 10 env OMP_NUM_THREADS=1 THREADS=1 $T/haar5 exhp $f 5 0 > $W/out_$i.txt 2>&1; } 2>&1 | tail -n 1 )
  used=$(awk -v a=$used -v b="$t" -v c="$t2" 'BEGIN{split(b,x," ");split(c,y," "); print a+x[1]+x[2]+y[1]+y[2]}')
  res=$(grep RESULT $W/out_$i.txt | tail -n 1)
  [ -z "$res" ] && res="NO_RESULT(rc or timeout) $(tail -n 1 $W/out_$i.txt)"
  echo "$i |G/G'|=$gp |Z|=$zc cpu_used=$used :: $res" >> $W/exh216.log
  rm -f $f
done < $W/ranked_run.txt
echo DONE used=$used >> $W/exh216.log
