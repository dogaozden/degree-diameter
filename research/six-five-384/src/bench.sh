#!/bin/bash
# bench.sh BINARY: run BINARY on the 3 benchmark groups (342_12: 10 VALID sets; 360_53: 41 side-A covers, 12 ASIDE
# lines; 384_11094: none), check the output equals the reference (all lines except the first; the DONE line without its prefixes= count), report user CPU seconds.
# Prints one line: "valid=<true|false> cpu=<seconds>" (valid only if all 3 outputs are identical to the references).
B=$(readlink -f $1); D=/tmp/claude-0/bench; ok=true; tot=0
for g in 342_12 360_53 384_11094; do
  t0=$(awk '{print $14+$15}' /proc/$$/stat)
  s=$( { TIMEFORMAT=%U; time $B $D/hx_$g.txt | grep -v "^N=" | sed "s/ prefixes=[0-9]*//" > /tmp/bench_$$_$g.out; } 2>&1 )
  tot=$(echo "$tot + $s" | bc)
  cmp -s /tmp/bench_$$_$g.out $D/ref_$g.out || ok=false
  rm -f /tmp/bench_$$_$g.out
done
echo "valid=$ok cpu=$tot"
