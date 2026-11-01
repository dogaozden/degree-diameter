#!/bin/bash
# gen37.sh ORDER ID N MAXSETS : c1 copy of src/gen_gsets.sh with a MAXSETS cap (enumeration order).
# MAXSETS=probe: no GAP run; re-probe the files listed in the existing gsets.list (for interrupted runs).
O=$1; I=$2; N=$3; M=$4
D=squad/r1/c1/gs/n${N}/g${O}_${I}; mkdir -p $D
if [ "$M" != "probe" ]; then
  echo "Read(\"src/gsets.g\");; G:=SmallGroup($O,$I);; Print(\"# \", StructureDescription(G), \"\\n\");; dosets(G, $N, \"$D\", \"g\", $M);; QUIT;" | gap -q > $D/gsets.list 2>&1
  sed -i ':a;/\\$/{N;s/\\\n//;ba}' $D/gsets.list
fi
grep "\.txt" $D/gsets.list | while read f desc; do
  [ -s "$f" ] || continue
  e=$(PROBE=300 timeout 20 bin/orbdfs $f 7 2>/dev/null | sed -n 's/.*nodes_est=\([^ ]*\).*/\1/p'); echo "$f ${e:-PROBE_TIMEOUT} $desc"; done > $D/est.new && mv $D/est.new $D/est.txt
echo "g${O}_${I} $(head -1 $D/gsets.list) sets=$(wc -l < $D/est.txt)"
