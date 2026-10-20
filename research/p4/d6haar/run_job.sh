#!/usr/bin/env bash
# One search job: run_job.sh D d G0 c seed seconds K   (builds the table if missing; logs to logs/, solution to sols/)
set -u
cd "$(dirname "$0")"
D=$1; d=$2; g=$3; c=$4; seed=$5; secs=$6; K=${7:-20}
tag="D${D}_d${d}_${g}_x${c}_s${seed}_K${K}"
[ -f sols/$tag.txt ] && { echo "skip $tag (solved)"; exit 0; }
[ -f logs/$tag.log ] && grep -q "best=" logs/$tag.log && { echo "skip $tag (done)"; exit 0; }
[ -f tables/$g.txt ] || python3 groups.py $g >/dev/null
nice -n 15 ./haar_dd $D $d tables/$g.txt $c $seed $secs sols/$tag.txt $K > logs/$tag.log 2>&1
tail -1 logs/$tag.log
