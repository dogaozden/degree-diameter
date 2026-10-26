#!/bin/bash
# usage: screen.sh SPECFILE FROM TO SECS SEED LOG
# Runs haar_fast (d=7, D=5, K=16) on lines FROM..TO of SPECFILE (format: "mu N meta p k r n # comment").
cd /home/user/degree-diameter/research/squads/hunt-d5/r3/b3 || exit 1
specfile=$1; from=$2; to=$3; secs=$4; seed=$5; log=$6
n=0
while read -r mu N meta p k r nn rest; do
  n=$((n+1))
  if [ "$n" -lt "$from" ] || [ "$n" -gt "$to" ]; then continue; fi
  out=$PWD/cost0_${N}_p${p}_k${k}_r${r}_n${nn}_s${seed}.bin
  line=$(THREADS=1 OMP_NUM_THREADS=1 timeout $((secs+30)) nice -n 10 ../../tools/haar_fast 7 5 "$secs" "$seed" 16 "$out" meta "$p" "$k" "$r" "$nn" 2>&1 | grep '^RESULT')
  echo "$N meta $p $k $r $nn seed=$seed $line" >> "$log"
done < "$specfile"
