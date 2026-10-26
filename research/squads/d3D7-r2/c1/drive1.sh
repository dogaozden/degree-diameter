#!/bin/bash
# round-2 c1 driver: one GA run at a time, 300 s each
C=/home/user/degree-diameter/research/squads/d3D7-r2/c1
G=/home/user/degree-diameter/research/d3D7/groups
cd $C
: > runs.tsv
run() { # p gfile gid seed secs tag
  local p=$1 gf=$2 id=$3 seed=$4 secs=$5 tag=$6
  timeout 900 nice -n 10 ./ga $p $G/$gf $id $seed $secs 30 $tag.sol > $tag.log 2>&1
  local N=$(head -1 $G/$gf >/dev/null; awk -v g=$id '$1=="G" && $3==g {print $2; exit}' $G/$gf)
  local best=$(grep "end best" $tag.log | awk '{print $3}')
  [ -z "$best" ] && best=NA
  printf "%s\t%s\t%s\t%s\t%s\t%s\n" "$(awk -v g=$id '$1=="G" && $3==g {print $4}' $G/$gf)" "$p" "$((2*p*N))" "$seed" "$best" "$tag" >> runs.tsv
}
run 6 g15.txt 1 1 300 c15p6
run 8 g11.txt 1 1 300 c11p8
run 7 g13.txt 1 1 300 c13p7
run 9 g10.txt 1 1 300 c10i1p9
run 9 g10.txt 2 1 300 c10i2p9
run 10 g9.txt 1 1 300 c9i1p10
run 10 g9.txt 2 1 300 c9i2p10
echo DONE >> runs.tsv
