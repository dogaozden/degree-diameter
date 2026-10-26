#!/bin/bash
# finish.sh X.sol OUT [SEED]: a coverage-0 dmhub state (free/sigma/hubgraph) -> coset-0 by dmfast_hub (RELAX=1 with the
# state's hub adjacency, targeted moves, then a hot polish if needed) -> exact dmhub cost with the same hub graph ->
# apsp.  Prints the final lines; writes OUT.sol / OUT.edges (dmhub) and OUT_*.log.
set -u
X=$1; O=$2; SEED=${3:-1}; D=$(cd "$(dirname "$0")" && pwd)
FREE=$(awk '$1=="free"{$1=""; print}' "$X")
H=$(awk '$1=="dmhub"{print $5}' "$X")
HUBADJ=$(awk -v H="$H" '$1=="hubgraph"{for(i=2;i<NF;i+=2) printf "%d:%d ", int($i/H), int($(i+1)/H)}' "$X")
python3 "$D/../hubs/sol2lift2.py" "$X" "${O}_l2.sol" > /dev/null
run_c0() {  # IN OUT log extra-env...
    local IN=$1 OUT=$2 LOG=$3; shift 3
    env FREE="$FREE" RELAX=1 HUBADJ="$HUBADJ" BASE="$D/gq/gq_q7.bin" NPOLY=4 SEED=$SEED IN="$IN" OUT="$OUT" "$@" \
        timeout 1200 nice -n 10 "$D/dmfast_hub" 7 > "$LOG" 2> "$LOG.err"
    awk '{print $6}' "$LOG"
}
b=$(run_c0 "${O}_l2.sol" "${O}_c0.sol" "${O}_c0.log" PTARG=0.5 SWAPP=0.01 ITERS=30000000 TEMP0=0.25 TEMP1=0.02)
echo "coset-0 after targeted run: $b"
for r in 1 2 3; do
    [ "$b" = "0" ] && break
    cp "${O}_c0.sol" "${O}_c0in.sol"
    b=$(run_c0 "${O}_c0in.sol" "${O}_c0.sol" "${O}_c0p$r.log" PTARG=1.0 SWAPP=0.05 ITERS=3000000 TEMP0=0.5 TEMP1=0.05 SEED=$((SEED+r)))
    echo "coset-0 after hot polish $r: $b"
done
[ "$b" = "0" ] || { echo "coset-0 not reached"; exit 1; }
env FREE="$FREE" HGFIRST=1 HGDIST=1 HUBG_IN="$X" ITERS=0 timeout 900 nice -n 10 "$D/dmhub" "$D/gq/gq_q7.bin" "${O}_c0.sol" "$O" > "${O}_exact.log"
grep -E 'cover cost final|final cost' "${O}_exact.log"
grep -q 'final cost 0 ' "${O}_exact.log" || { echo "exact cost not 0"; exit 1; }
"$D/apsp" "$O.edges" 10 5 | tail -n 3
