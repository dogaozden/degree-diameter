#!/bin/bash
# RESTART=1 on the 120,120 groups (fresh random orbits on each reheat). usage: restart.sh OUTDIR
out="$(cd "$1" && pwd)"; cd "$(dirname "$0")/../.." || exit 1
run() { tag="$1"; seed="$2"; shift 2
  env RESTART=1 ORBIT="3 2 2" THREADS=1 nice -n 5 timeout 1320 ./haar_sym 8 8 1200 "$seed" 8 "$out/$tag.txt" "$@" > "$out/$tag.log" 2>&1; }
run d8D8_psl_11_182_RST_s9 9 psl 11 182 &
run d8D8_psl_11_182_RST_s10 10 psl 11 182 &
run d8D8_sl_11_91_RST_s9 9 sl 11 91 &
run d8D8_prod_psl_7_sl_9_1_RST_s9 9 prod psl 7 sl 9 1 &
wait; echo "restart done"
