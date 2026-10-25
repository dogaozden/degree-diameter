#!/bin/bash
# fdexact.sh IN.sol "FDSET" OUT SEED [SECS ITERS T0]: exact-BFS annealing of sigma and nu (dmhub2_f main loop: targeted
# nu flips on the geodesics of bad pairs, sigma swaps) for the per-flag FLAGDEL graph, then an independent rebuild
# (build_fd.py) and apsp.
IN=$1; FS=$2; O=$3; SD=$4; SECS=${5:-600}; IT=${6:-60000}; T0=${7:-0.6}
python3 ../hubs/sol2lift2.py "$IN" "${O}_in_l2.sol" > /dev/null
FREE="$(awk '$1=="free"{$1="";print}' "$IN")" H=3 FLAGDEL=1 FDSET="$FS" HUBG_IN="$IN" ITERS=$IT SECS=$SECS T0=$T0 T1=0.03 \
  PNU=0.8 PTARG=0.8 FOCUS=0.8 SEED=$SD timeout $((SECS + 300)) nice -n 5 ./dmhub2_f gq/gq_q7.bin "${O}_in_l2.sol" "$O" > "$O.log" 2>&1
grep -E 'initial cost|final cost' "$O.log"
python3 build_fd.py gq/gq_q7.bin "$O.sol" "$FS" "$O.fd.edges" && ./apsp "$O.fd.edges" 10 5 | tail -n 2
