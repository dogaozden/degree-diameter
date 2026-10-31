#!/bin/bash
# launch.sh TAG SEED "GROUP" [VAR=x ...]: start one orbit search (k=3, m=3, f=1) in runs/, resumable via runs/TAG.ckpt
cd /home/user/degree-diameter/research/d10D8/runs || exit 1
tag=$1; seed=$2; grp=$3; shift 3
env ORBIT="3 3 1" CKPT=$tag.ckpt "$@" nohup nice -n 5 timeout 30000 ../sym2/haar_sym2 10 8 28000 $seed 8 $tag.txt $grp > $tag.out 2>> $tag.log &
