#!/bin/bash
# usage: run_one.sh SECS SEED GROUP_KIND Q N_CYC
secs=$1; seed=$2; kind=$3; q=$4; n=$5
tag="d16D5_${kind}_${q}_n${n}_s${seed}"
out=/home/user/degree-diameter/research/squads/alone/1/runs/$tag.sol
log=/home/user/degree-diameter/research/squads/alone/1/runs/$tag.log
THREADS=1 $HOME/hg3 16 5 $secs $seed 1 $out $kind $q $n > $log 2>&1
echo "$tag $(grep RESULT $log)"
