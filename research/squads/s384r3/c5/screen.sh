#!/bin/bash
# usage: screen.sh SECS SEED GROUP_ID... ; appends "group base cost" lines to screen.tsv
cd /home/user/degree-diameter/research/squads/s384r3/c5 || exit 1
SECS=$1; SEED=$2; shift 2
for g in "$@"; do
  for bi in $(seq -w 0 16); do
    b=m$bi
    out=runs/${g}_${b}_s${SEED}_t${SECS}
    SECS=$SECS SEED=$SEED INIT=random timeout 60 ./bin/tabu bases/$b.txt groups/$g.txt $out.sol > $out.log 2> $out.err
    c=$(awk '/^RESULT/{print $3}' $out.log)
    echo "$g $b $c" >> screen.tsv
  done
done
