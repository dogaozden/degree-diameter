#!/usr/bin/env bash
# One search job: run_job.sh D d G0 c seed seconds K   (group G0 x Z_c, or G0 x c when c is a group name; builds the table if missing; logs to logs/, solution to sols/)
# The body is one { } block so bash parses it whole: editing this file while jobs run cannot break them.
{
set -u
cd "$(dirname "$0")"
mkdir -p logs sols graphs tables
D=$1; d=$2; g=$3; c=$4; seed=$5; secs=$6; K=${7:-20}
tag="D${D}_d${d}_${g}_x${c}_s${seed}_K${K}"
[ -f sols/$tag.txt ] && { echo "skip $tag (solved)"; exit 0; }
[ -f logs/$tag.log ] && grep -q "best=" logs/$tag.log && { echo "skip $tag (done)"; exit 0; }
[ -f tables/$g.txt ] || python3 groups.py $g >/dev/null
carg=$c
case $c in *[!0-9]*) [ -f tables/$c.txt ] || python3 groups.py $c >/dev/null; carg=tables/$c.txt;; esac   # second factor: a group name (haar_dd2 only)
bin=./haar_dd; [ -x ./haar_dd2 ] && bin=./haar_dd2   # haar_dd2: faster at odd D, same at even D, takes a second table
nice -n 15 $bin $D $d tables/$g.txt $carg $seed $secs sols/$tag.txt $K > logs/$tag.log 2>&1
tail -1 logs/$tag.log
exit 0
}
