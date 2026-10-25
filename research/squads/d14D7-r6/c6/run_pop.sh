#!/bin/bash
# population phase: short annealers from scratch, one process at a time, single thread
export OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 NUMEXPR_NUM_THREADS=1
SC=/tmp/claude-0/-home-user-degree-diameter/0a251e0c-8f17-58ce-a4f2-34eda2ea0db1/scratchpad/r6_c6
cd /home/user/degree-diameter/research/squads/d14D7-r6/c6
mkdir -p $SC/pop
for s in "$@"; do
  timeout 900 nice -n 15 python3 mirror_sa4.py $s $SC/pop/s$s --secs 120 > $SC/pop_$s.log 2>&1
done
echo POP_DONE
