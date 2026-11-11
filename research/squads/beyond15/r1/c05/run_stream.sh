#!/bin/bash
# usage: run_stream.sh d D secs "seeds"   (reads groups.json; each k, each seed; logs in runs/)
F=/home/user/degree-diameter/research/frontier
DIR=/home/user/degree-diameter/research/squads/beyond15/r1/c05
d=$1; D=$2; secs=$3; SEEDS=$4
for k in 13 19 31 43 61 97 151 211 307; do
  line=$(python3 -c "import json;g=json.load(open('$DIR/groups.json'));v=g.get('$d,$D,$k');print('' if v is None else ' '.join(str(x) for x in v[:4]))")
  if [ -z "$line" ]; then echo "skip $d $D $k" >> $DIR/runs/skipped.txt; continue; fi
  set -- $line
  m=$1; kk=$2; r=$3
  for seed in $SEEDS; do
    name=$DIR/runs/d${d}D${D}_k${k}_s${seed}
    env T0=8 T1=1 REHEAT=400 THREADS=1 timeout 105 nice -n 10 $F/bin/hmeta $d $D $secs $seed 8 $name.sol $m $kk $r > $name.log 2>&1
  done
done
echo DONE > $DIR/runs/done_${d}_${D}.txt
