#!/bin/bash
# usage: sweep.sh TAG SECS SEED "name base group" ...   (one vl run per entry, sequential)
C=/home/user/degree-diameter/research/squads/bh5-r1/c5
tag=$1; secs=$2; seed=$3; shift 3
for item in "$@"; do
  set -- $item
  name=$1; base=$2; grp=$3
  res=$(cd /home/user/degree-diameter/research/beyond-haar-d5 && D=5 INC=1 SECS=$secs SEED=$seed OUT=$C/sols/$name.sol timeout $((secs+90)) nice -n 10 ./vl $C/$base $C/groups/$grp 2>>$C/logs/$name.err | grep RESULT)
  echo "$tag $name $base $grp secs=$secs seed=$seed :: $res" >> $C/results.txt
done
