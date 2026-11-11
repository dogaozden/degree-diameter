#!/bin/bash
# i16: exhaustive cubic Haar scan H(G,{e,x,y}) (exh3) over many small groups, D = 9 and D = 10
B=/home/user/degree-diameter/research/frontier/beyond13
W=/home/user/degree-diameter/research/squads/beyond13/r6/i16
export THREADS=1
NAMES="agl_17 agl_19 agl_23 heis_7 gl_5 sl_5__x__cyc_3 sl_5__x__cyc_4 pgl_5__x__cyc_3 pgl_5__x__cyc_4 psl_5__x__cyc_5 psl_5__x__cyc_6 psl_5__x__cyc_8 psl_9 sl_8 psl_7__x__cyc_2 psl_11 sl_9 agl_25 psl_5__x__cyc_7 sl_5__x__cyc_7 psl_7__x__cyc_3 sl_7__x__cyc_2"
for nm in $NAMES; do
  if [ ! -f $W/out/tab_$nm.bin ]; then
    timeout 100 nice -n 10 python3 $W/mktab.py $nm > /dev/null 2>&1 || { echo "TABFAIL $nm"; continue; }
  fi
  for D in 9 10; do
    timeout 100 nice -n 10 $B/bin/exh3 $W/out/tab_$nm.bin $D $W/out/exh_${nm}_d$D 2>&1 | grep -E "GROUP|RESULT" | tr '\n' ' '
    echo
  done
done
echo SCANDONE
