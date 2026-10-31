#!/bin/bash
# mintime.sh BIN... : min user CPU seconds over 2 runs on the 384 benchmark group, interleaved
for r in 1 2; do for B in "$@"; do
  t=$( { TIMEFORMAT=%U; time $B /tmp/claude-0/bench/hx_384_11094.txt > /dev/null; } 2>&1 )
  echo "$B $t"
done; done | awk '{ if (!($1 in m) || $2 < m[$1]) m[$1] = $2 } END { for (b in m) print b, m[b] }'
