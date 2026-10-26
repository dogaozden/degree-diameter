#!/bin/bash
# usage: screen.sh  -> runs ga 60 s on every target, appends "N id name p n best" to runs.tsv
R=/home/user/degree-diameter
GA=$R/research/squads/d3D7-r1/c9/ga
C=$R/research/squads/d3D7-r2/c2
cd $C
: > runs.tsv
run() { # GROUPS p id name order
  local G=$1 p=$2 id=$3 name=$4 N=$5
  local tag="g${N}_${id}_p${p}"
  timeout 900 nice -n 10 $GA $p $R/research/d3D7/groups/$G $id 1 60 30 $C/$tag.sol > $C/$tag.log 2>&1
  local best=$(grep '^end best' $C/$tag.log | awk '{print $3}')
  [ -z "$best" ] && best=$(grep -c FOUND $C/$tag.log | sed 's/^1$/0/;s/^0$/NA/')
  printf "%s %s %s %s %s %s\n" $N $id "$name" $p $((2*p*N)) "$best" >> $C/runs.tsv
}
for line in $(grep '^G 16 ' $R/research/d3D7/groups/g16.txt | awk '{print $3":"$4}'); do
  id=${line%%:*}; name=${line#*:}; run g16.txt 6 $id "$name" 16; done
for line in $(grep '^G 12 ' $R/research/d3D7/groups/g12.txt | awk '{print $3":"$4}'); do
  id=${line%%:*}; name=${line#*:}; run g12.txt 8 $id "$name" 12; done
for line in $(grep '^G 14 ' $R/research/d3D7/groups/g14.txt | awk '{print $3":"$4}'); do
  id=${line%%:*}; name=${line#*:}; run g14.txt 7 $id "$name" 14; done
echo DONE
