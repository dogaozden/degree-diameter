#!/bin/bash
# usage: drive.sh groupsfile secs NB STALL logfile
cd /home/user/degree-diameter/research/squads/beyond-small/r1/c10
GF=$1; SECS=$2; NB=$3; ST=$4; LOG=$5
i=0
while read n k r u v N; do
  i=$((i+1))
  for nfix in 0 2; do
    nice -n 10 ./tabu $n $k $r $u $v $nfix $((i*10+nfix+1)) $SECS $NB $ST found/g${N}_${n}_${k}_${r}_${u}_${v}_f${nfix}.txt 2>/dev/null >> $LOG
  done
done < $GF
echo DONE >> $LOG
