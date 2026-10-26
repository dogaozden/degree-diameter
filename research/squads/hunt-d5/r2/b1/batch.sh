#!/bin/bash
# usage: batch.sh FIRST_SEED LAST_SEED ; runs haar5 anneal on SmallGroup(615,1), d=7, 10 s per seed
export OMP_NUM_THREADS=1 THREADS=1
cd /home/user/degree-diameter/research/squads/hunt-d5/r2/b1
Ks=(8 16 32); Cs=(5 20)
for s in $(seq "$1" "$2"); do
  K=${Ks[$((s % 3))]}; C=${Cs[$(((s / 3) % 2))]}
  line=$(K=$K COOL=$C RESTART=1 timeout 40 nice -n 10 ../../tools/haar5 anneal ../../tables/g615_1.bin 7 10 $s "sol_s${s}.txt" 2>/dev/null | grep '^RESULT')
  echo "seed=$s K=$K COOL=$C $line" >> runs.txt
done
