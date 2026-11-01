#!/bin/bash
# usage: scr.sh GROUPTAG BIN SECONDS CFG... : anneal each cfg, append one line per cfg to screen/results.tsv
tag=$1; bin=$2; secs=$3; shift 3
for c in "$@"; do
  r=$(CYCLE=$(( secs / 3 > 8 ? secs / 3 : 8 )) timeout 120 nice -n 10 /home/user/degree-diameter/research/squads/handsoff-49/w17/mix $bin $c $secs 7 9 0 $(awk "BEGIN{print 0.12*2520}") $(awk "BEGIN{print 0.004*2520}") | tail -1)
  echo -e "$tag\t$(basename $c .cfg)\t$r" | tee -a /home/user/degree-diameter/research/squads/handsoff-49/w17/screen/results.tsv
done
