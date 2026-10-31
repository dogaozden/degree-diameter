#!/bin/bash
# usage: restart.sh NAME GROUPFILE STARTFILE SECS SEED T0 T1 : SA (symloc, same-side cost) from a given G-invariant graph
cd /home/user/degree-diameter/research/squads/handsoff-37/r3a
name=$1; grp=$2; st=$3; secs=$4; seed=$5; T0=$6; T1=$7
d=out/$name/s$seed; mkdir -p $d
timeout 100 nice -n 10 ./symloc $grp $st $((secs*40000)) $T0 $T1 $secs $seed $d/sa > $d/sa.out 2> $d/sa.log
far=$(grep "done best" $d/sa.log | awk '{print $3}')
bf=$(../bin/score37 $d/sa_best.edges 2>/dev/null | tail -1)
echo -e "$name\trestart\tseed=$seed\tT=$T0->$T1\tcost=$far\t$bf" >> out/results.tsv
echo "$name seed=$seed T=$T0->$T1 cost=$far | $bf"
