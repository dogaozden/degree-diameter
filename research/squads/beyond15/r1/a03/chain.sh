#!/bin/bash
cd /home/user/degree-diameter/research/squads/beyond15/r1/a03/chain
F=/home/user/degree-diameter/research/frontier
B=$F/beyond13/lifts/bases
R=/home/user/degree-diameter/research/squads/beyond15/r1/a03/rank
chainrun() { # name base n start_file
  local name=$1 base=$2 n=$3 st=$4 prev=$4
  for k in 1 2 3; do
    out=${name}_L$k
    if [ "$k" = 2 ]; then cmd=$F/bin/scan; sec=90; else cmd=$F/bin/lift; sec=90; fi
    if [ "$k" = 2 ]; then
      env START=$prev THREADS=1 timeout 100 nice -n 10 $cmd $base $n 15 $sec $((10+k)) $out 6 > $out.log 2>&1
    else
      env START=$prev THREADS=1 timeout 100 nice -n 10 $cmd $base $n 15 $sec $((10+k)) $out 2.0 0.05 1200 > $out.log 2>&1
    fi
    echo "$name link$k: $(grep -i -E 'result|best' $out.log | tail -1)" >> summary.txt
    if [ -f $out.best ]; then prev=$out.best; fi
    if [ -f $out.edges ]; then echo "$name FOUND $out.edges" >> summary.txt; return; fi
  done
}
chainrun gp12_5 $B/gp12_5.txt 437 $R/gp12_5.best
chainrun tutte8 /home/user/degree-diameter/research/squads/beyond15/r1/a03/tutte8.txt 350 $R/tutte8.best
echo DONE >> summary.txt
