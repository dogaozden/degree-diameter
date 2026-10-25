#!/bin/bash
# warm start: IN is a design at Z_m (orbit ids kept in the 4th field); set the modulus to m2 keeping every voltage,
# then symrepair (D=6, C-invariant) and the full all-source check.
C=/home/user/degree-diameter/research/squads/d16D8-r3/c5
S=/home/user/degree-diameter/research/d16D8
IN=$1; m2=$2; secs=$3; seed=$4; tag=$5
OUT=$C/runs/warm_${tag}_m${m2}.base
awk -v m=$m2 'NR==1{$2=m} {print}' $IN > $OUT
echo "warm m=$m2 from $IN seed=$seed"
SRCFILE=$C/runs/rand_m32_s1.src THREADS=1 timeout 1500 nice -n 10 $S/symrepair $OUT 6 $secs $seed $C/runs/wrep_${tag}_m${m2}.base 2>&1 | grep -E "RESULT|start full" | tail -2
env -u SRCFILE THREADS=1 timeout 1500 nice -n 10 $S/baselift eval $C/runs/wrep_${tag}_m${m2}.base 6
