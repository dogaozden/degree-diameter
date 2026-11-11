#!/bin/bash
# chunk.sh GID SEED CHUNK SECS TMO T0 T1 : one short anneal chunk on group GID (1..6), voltages only (base fixed)
G=$1; S=$2; C=$3; SECS=$4; TMO=$5; T0=$6; T1=$7
D=/home/user/degree-diameter/research/squads/beyond14/r6/h09
B=$D/runs/g${G}_s${S}
ST=""
if [ -s $B.sol.best ]; then ST="$B.sol.best"; fi
if [ -n "$ST" ]; then
  timeout $TMO nice -n 10 env THREADS=1 FIXBASE=1 D=14 START=$ST $D/salift_e16 2 $D/tabs_h09.txt $G $((S*1000+C)) $SECS $T0 $T1 $B.sol > $B.log.$C 2>&1
else
  timeout $TMO nice -n 10 env THREADS=1 FIXBASE=1 D=14 $D/salift_e16 2 $D/tabs_h09.txt $G $((S*1000+C)) $SECS $T0 $T1 $B.sol > $B.log.$C 2>&1
fi
echo "g$G s$S c$C: $(grep -c . $B.log.$C) lines; last: $(grep -E 'best|FOUND' $B.log.$C | tail -1)"
[ -s $B.sol.best ] && echo "  best file: $(head -1 $B.sol.best)"
