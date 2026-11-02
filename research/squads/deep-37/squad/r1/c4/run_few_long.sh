#!/bin/bash
# run_few.sh ORDER ID N MAXR CAP : write the CAP G-sets with fewest orbits for SmallGroup(ORDER,ID), then PROBE each
O=$1; I=$2; N=$3; R=$4; C=$5
D=squad/r1/c4/gs/n${N}/g${O}_${I}; mkdir -p $D
echo "G:=SmallGroup($O,$I);; Print(\"# \", StructureDescription(G), \" order \", Size(G), \"\\n\");; dofew(G, $N, \"$D\", \"f\", $R, $C);; QUIT;" > $D/driver.g
( echo "Read(\"squad/r1/c4/gsets_few.g\");;"; cat $D/driver.g ) | timeout 200 nice -n 15 gap -q > $D/gsets.list 2>&1
rm -f $D/driver.g
: > $D/est.txt
for f in $(ls $D/f_[0-9]*.txt 2>/dev/null | sort -t_ -k2 -n); do
  e=$(PROBE=300 timeout 5 nice -n 15 bin/orbdfs $f 7 2>/dev/null | sed -n 's/.*nodes_est=\([^ ]*\).*/\1/p'); echo "$f ${e:-PROBE_TIMEOUT} $(grep "^$f " $D/f_list.txt | cut -d' ' -f2-)" >> $D/est.txt
done
echo "g${O}_${I} $(head -1 $D/gsets.list) files=$(ls $D/f_[0-9]*.txt 2>/dev/null | wc -l)"
