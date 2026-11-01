#!/bin/bash
# gen_gsets.sh ORDER ID N : write all admissible G-sets of SmallGroup(ORDER,ID) on N vertices + Knuth estimates
O=$1; I=$2; N=$3
D=${OUT:-runs/sweep}/n${N}/g${O}_${I}; mkdir -p $D
echo "Read(\"src/gsets.g\");; G:=SmallGroup($O,$I);; Print(\"# \", StructureDescription(G), \"\\n\");; dosets(G, $N, \"$D\", \"g\", 100000);; QUIT;" | gap -q > $D/gsets.list 2>&1
sed -i ':a;/\\$/{N;s/\\\n//;ba}' $D/gsets.list
grep "\.txt" $D/gsets.list | while read f desc; do
  e=$(PROBE=300 timeout 20 bin/orbdfs $f 7 2>/dev/null | sed -n 's/.*nodes_est=\([^ ]*\).*/\1/p'); echo "$f ${e:-PROBE_TIMEOUT} $desc"; done > $D/est.txt
echo "g${O}_${I} $(head -1 $D/gsets.list) sets=$(wc -l < $D/est.txt)"
