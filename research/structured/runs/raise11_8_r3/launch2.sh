#!/bin/bash
# Round 3 (raise11_8), batch 2: four plain orbit-anneal runs on psl 19 x Z331, EXH off, state dump on.
cd /home/user/degree-diameter/research/structured
for s in 35 36 37 38; do
  ORBIT="5 2 1" ORBW=5 K=8 THREADS=1 DUMP=runs/raise11_8_r3/psl19_331_s$s.dump \
    nice -n 5 timeout 9900 ./haar_sym_r3 11 8 9000 $s 8 /home/user/degree-diameter/research/frontier/sols/d11D8_psl_19_331_orb5_R3_s$s.txt psl 19 331 \
    > runs/raise11_8_r3/psl19_331_s$s.log 2>&1 &
done
wait
