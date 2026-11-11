#!/bin/bash
# job.sh D secs N m k r tag  -> runs hmeta (4 D) for secs seconds, one thread, low priority
D=$1; S=$2; N=$3; M=$4; K=$5; R=$6; TAG=$7
cd /home/user/degree-diameter/research/squads/beyond13/r6/i09
THREADS=1 T0=8 T1=1 REHEAT=400 timeout $((S+20)) nice -n 10 /home/user/degree-diameter/research/frontier/beyond13/meta/hmeta 4 $D $S ${RANDOM} 8 runs/${TAG}_${M}_${K}_${R} $M $K $R > runs/${TAG}_${M}_${K}_${R}.log 2>&1
