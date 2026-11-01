#!/bin/bash
# sweep.sh ORDER ID N TLIMIT PAR : all admissible G-sets of SmallGroup(ORDER,ID) on N vertices, orbdfs each (D = 7)
O=$1; I=$2; N=$3; T=$4; PAR=${5:-2}
D=runs/sweep/n${N}/g${O}_${I}; mkdir -p $D
echo "Read(\"src/gsets.g\");; G:=SmallGroup($O,$I);; Print(\"# \", StructureDescription(G), \"\\n\");; dosets(G, $N, \"$D\", \"g\", 100000);; QUIT;" | gap -q > $D/gsets.list 2>&1
sed -i ':a;/\\$/{N;s/\\\n//;ba}' $D/gsets.list
grep "\.txt" $D/gsets.list | awk '{print $1}' | xargs -P $PAR -I{} bash -c 'f={}; r=$(MAXSOL=50 SOLPREFIX=${f%.txt}_sol timeout '$T' bin/orbdfs $f 7 2>/dev/null | grep DONE); [ -z "$r" ] && r="TIMEOUT"; echo "$f $r"' > $D/results.txt
echo "g${O}_${I} $(head -1 $D/gsets.list) sets=$(grep -c '\.txt' $D/gsets.list) done=$(grep -c DONE $D/results.txt) timeout=$(grep -c TIMEOUT $D/results.txt) sols=$(awk '{for(i=1;i<=NF;i++) if($i ~ /^sols=/){split($i,a,"="); s+=a[2]}} END{print s+0}' $D/results.txt)"
