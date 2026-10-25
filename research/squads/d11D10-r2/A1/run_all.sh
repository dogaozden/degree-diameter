#!/bin/bash
# A1 driver, run as ONE gated job (one slot wait): build the per-sample copy, then six RANDORB=150 screens.
A=/home/user/degree-diameter/research/squads/d11D10-r2/A1
H=$A/haar_sym_A1
cd "$A" || exit 1
gcc -O3 -march=native -fopenmp -o haar_sym_A1 haar_sym_A1.c -lm || { echo "$(date +%T) build failed" >> driver.log; exit 1; }
echo "$(date +%T) built haar_sym_A1" >> driver.log
run() {   # run TAG AFROB AR
  echo "$(date +%T) start $1" >> driver.log
  env -u THREADS OMP_NUM_THREADS=1 RANDLOG=1 ORBIT="10 1 1" AFROB=${2} AFROBH="0 1 2 0" AR=${3} RANDORB=150 RANDB=1000000 \
    "$H" 11 10 60 31 8 "$A/d11D10_psl_243_11_orb10_afrob${2}_ar${3}_s31.txt" psl 243 11 > "$A/randorb_$1.log" 2>&1
  echo "$(date +%T) done $1 rc=$?" >> driver.log
}
run afrob1_ar2 1 2
run afrob2_ar2 2 2
run afrob3_ar2 3 2
run afrob4_ar2 4 2
run afrob1_ar6 1 6
run afrob1_ar7 1 7
echo "$(date +%T) driver finished" >> driver.log
