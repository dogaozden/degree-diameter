#!/bin/bash
# remaining targets at 30 s each (time box); same format as runs.tsv, with a seconds column appended
R=/home/user/degree-diameter
GA=$R/research/squads/d3D7-r1/c9/ga
C=$R/research/squads/d3D7-r2/c2
cd $C
run() { # GROUPS p id name order
  local G=$1 p=$2 id=$3 name=$4 N=$5
  local tag="g${N}_${id}_p${p}"
  timeout 900 nice -n 10 $GA $p $R/research/d3D7/groups/$G $id 1 30 30 $C/$tag.sol > $C/$tag.log 2>&1
  local best=$(grep '^end best' $C/$tag.log | awk '{print $3}')
  printf "%s %s %s %s %s %s 30s\n" $N $id "$name" $p $((2*p*N)) "$best" >> $C/runs.tsv
}
for line in $(grep '^G 16 ' $R/research/d3D7/groups/g16.txt | awk '{print $3":"$4}'); do
  id=${line%%:*}; name=${line#*:}; if [ $id -ge 6 ]; then run g16.txt 6 $id "$name" 16; fi; done
for line in $(grep '^G 12 ' $R/research/d3D7/groups/g12.txt | awk '{print $3":"$4}'); do
  id=${line%%:*}; name=${line#*:}; run g12.txt 8 $id "$name" 12; done
for line in $(grep '^G 14 ' $R/research/d3D7/groups/g14.txt | awk '{print $3":"$4}'); do
  id=${line%%:*}; name=${line#*:}; run g14.txt 7 $id "$name" 14; done
echo DONE
