#!/bin/bash
# usage: ev.sh SOLFILE  -> prints cost, N, file (uses hmeta EVAL with m k r parsed from the header)
f="$1"
read d D _ m k r _ <<< "$(head -1 "$f")"
out=$(timeout 105 nice -n 10 env THREADS=1 EVAL="$f" /home/user/degree-diameter/research/frontier/beyond14/bin/hmeta $d $D 1 1 1 /dev/null $m $k $r 2>&1 | grep EVAL)
echo "$f m=$m k=$k r=$r $out"
