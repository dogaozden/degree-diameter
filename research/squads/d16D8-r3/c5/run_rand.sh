#!/bin/bash
# random C_85-invariant start at Z_m, symrepair (D=6), then full all-source check
C=/home/user/degree-diameter/research/squads/d16D8-r3/c5
S=/home/user/degree-diameter/research/d16D8
G=/home/user/degree-diameter/research/squads/d16D8-r2/c4/group_q13.json
m=$1; seed=$2; secs=$3
python3 -B $S/symbase.py gq 13 $G $m $seed $C/runs/rand_m${m}_s${seed}.base $C/runs/rand_m${m}_s${seed}.src > /dev/null
echo "m=$m seed=$seed"
SRCFILE=$C/runs/rand_m${m}_s${seed}.src THREADS=1 timeout 1500 nice -n 10 $S/symrepair $C/runs/rand_m${m}_s${seed}.base 6 $secs $seed $C/runs/rep_m${m}_s${seed}.base 2>&1 | grep -E "RESULT|start full" | tail -2
env -u SRCFILE THREADS=1 timeout 1500 nice -n 10 $S/baselift eval $C/runs/rep_m${m}_s${seed}.base 6
