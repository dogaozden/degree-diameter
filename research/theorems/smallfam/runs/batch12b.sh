#!/bin/sh
# Heis(F_{p^2}) x| C_k (the family of the (4,7) graph), annealed with hanneal (fixed deadline), 3 seeds x 120 s
cd "$(dirname "$0")/.."
SP=/tmp/claude-0/-home-user-degree-diameter/2c3fb1ba-9359-5c52-a9c4-6d81a7db2df8/scratchpad
for spec in "9 5 24 1" "9 5 24 2" "9 7 8 6" "9 7 8 12" "8 5 12 4" "8 7 4 12" "8 7 4 24"; do
  set -- $spec; D=$1; p=$2; k=$3; e=$4
  tab=$SP/hq_${p}_${k}_${e}.txt
  [ -s $tab ] || nice -n 5 python3 heisq.py $p $k $e $tab > /dev/null
  desc="Heis(F_$((p*p))) x| C_$k, action lambda^$e"
  for s in 1 2 3; do
    r=$(nice -n 5 ./hanneal $tab 4 $D 120 $s 8 runs/heisq_sol_D${D}_${p}_${k}_${e}_s$s.txt 2>/dev/null | tail -1)
    echo "D=$D $desc seed=$s $r" >> runs/heisq_anneal.txt
    case "$r" in *best=0*) break;; esac
  done
  rm -f $tab
done
echo ALLDONE >> runs/heisq_anneal.txt
