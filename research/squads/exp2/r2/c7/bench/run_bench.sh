#!/bin/bash
# sequential benchmark (one process at a time): baseline = pristine hexd7 copy, new = two-down proxy
C=/home/user/degree-diameter/research/squads/exp2/r2/c7
HG=/home/user/degree-diameter/research/squads/exp2/r2/shared/rnd24.hg
cd "$C" || exit 1
for s in 1 2; do
  for v in base d2; do
    if [ "$v" = base ]; then BIN="$C/d7hex_base"; else BIN="$C/d7hex_d2"; fi
    t0=$(date +%s)
    BESTK=6 SKIPFULL=1 timeout 900 nice -n 10 "$BIN" search hex/hex_q5.bin 0 "$s" 600 "bench/${v}_s${s}.sol" 3 3 4 "$HG" \
      > "bench/${v}_s${s}.out" 2> "bench/${v}_s${s}.err"
    rc=$?
    t1=$(date +%s)
    echo "exit=$rc wall=$((t1 - t0))s" >> "bench/${v}_s${s}.out"
  done
done
echo done > bench/ALL_DONE
