#!/bin/bash
# finish_fd.sh STATE.sol C0.lift2.sol "FDSET" OUT: exact dmhub2_f cost of the coset-0 solution C0 (sigma, nu) with the
# hub graph of STATE (H=3 numbering), then the independent rebuild build_fd.py and apsp.
X=$1; C0=$2; FS=$3; O=$4
FREE="$(awk '$1=="free"{$1="";print}' "$X")" H=3 FLAGDEL=1 FDSET="$FS" HUBG_IN="$X" ITERS=0 timeout 600 nice -n 5 ./dmhub2_f gq/gq_q7.bin "$C0" "$O" > "$O.log" 2>&1
grep -E 'final cost' "$O.log"
python3 build_fd.py gq/gq_q7.bin "$O.sol" "$FS" "$O.fd.edges" && ./apsp "$O.fd.edges" 10 5 | tail -n 2
