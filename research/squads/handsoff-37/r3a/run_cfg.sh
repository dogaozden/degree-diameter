#!/bin/bash
# usage: run_cfg.sh NAME M K ALPHA SIGA SIGB SECS SEED T0 T1
set -u
name=$1; m=$2; k=$3; al=$4; sa=$5; sb=$6; secs=$7; seed=$8; T0=$9; T1=${10}
cd /home/user/degree-diameter/research/squads/handsoff-37/r2f
mkdir -p out/$name
python3 mkgroup.py $m $k $al "$sa" "$sb" out/$name/grp.txt out/$name/start.txt $seed > out/$name/mk_$seed.log 2>&1 || { echo "mkgroup failed"; cat out/$name/mk_$seed.log | tail -3; exit 1; }
head -1 out/$name/mk_$seed.log
nice -n 10 ./symloc out/$name/grp.txt out/$name/start.txt $((secs*25000)) $T0 $T1 $secs $seed out/$name/s$seed 2> out/$name/s$seed.log
echo "name=$name m=$m k=$k alpha=$al sA=$sa sB=$sb seed=$seed n=$((2*k*m))"
tail -1 out/$name/s$seed.log
grep "NEW BEST" out/$name/s$seed.log | tail -1
../bin/score37 out/$name/s${seed}_best.edges | tail -1
