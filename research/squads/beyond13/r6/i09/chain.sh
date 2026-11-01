#!/bin/bash
# chain.sh D N M K R START_OR_NONE LINKS SECS TAG : successive hmeta links, each starting from the previous .best
cd /home/user/degree-diameter/research/squads/beyond13/r6/i09
H=/home/user/degree-diameter/research/frontier/beyond13/meta/hmeta
D=$1; M=$3; K=$4; R=$5; ST=$6; L=$7; S=$8; TAG=$9
for i in $(seq 1 $L); do
  out=runs/${TAG}_$i
  if [ "$ST" != "none" ] && [ -f "$ST" ]; then export START=$ST; else unset START; fi
  THREADS=1 T0=8 T1=1 REHEAT=400 timeout $((S+20)) nice -n 10 $H 4 $D $S $((RANDOM*7+i)) 8 $out $M $K $R > $out.log 2>&1
  if [ -f $out.best ]; then ST=$out.best; fi
  grep -h RESULT $out.log
  if [ -f $out ]; then echo "SOLVED $out"; break; fi
done
echo CHAIN_DONE
