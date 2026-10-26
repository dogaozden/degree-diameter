#!/bin/bash
# h03: orbit-reduced exhaustive 2+2 scan at (3,10) for every group in index.txt (orders 217..230), one at a time
T=/home/user/degree-diameter/research/squads/b48/tools
H=/home/user/degree-diameter/research/squads/b48/r4/h03
cd $H
while read -r N rest; do fn=${rest##* }; name=$(echo "$rest" | tr " " "_" | sed "s/[/]/_/g");
  b=$(basename $fn .bin)
  python3 triples.py $fn > res/$b.in 2> res/$b.cnt
  LIMIT=8 ONLYLOW=1 timeout 120 nice -n 10 $T/flift $T/bases/cubic/b22_cubic.txt $fn 3 10 eval < res/$b.in > res/$b.out 2> res/$b.err
  echo "$N $b ${name:0:40} $(cat res/$b.cnt | sed 's/.*lines=//') min $(tail -1 res/$b.err | awk '{print $NF}')"
done < index.txt
