#!/bin/bash
cd /home/user/degree-diameter/research/squads/d13D7_r2/c2
export OMP_NUM_THREADS=1
while pgrep -f "clq_multi dirs1" > /dev/null; do sleep 2; done
timeout 900 nice -n 10 ./clq_multi dirs2.txt 11 150 m2_offsets.txt > m2_run.log 2>&1
timeout 900 nice -n 10 ./clq_multi dirs3.txt 12 150 m3_offsets.txt > m3_run.log 2>&1
echo chain_done > chain.done
