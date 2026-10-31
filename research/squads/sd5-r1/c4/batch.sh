#!/bin/bash
C=/home/user/degree-diameter/research/squads/sd5-r1/c4
while read n id t nc ab; do
  $C/run_group.sh $n $id 60
  echo "$n $id nc=$nc done $(date +%T)" >> $C/logs/batch_progress.txt
done < $C/lists/order.txt
echo BATCHDONE >> $C/logs/batch_progress.txt
