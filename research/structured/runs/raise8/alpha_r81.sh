#!/bin/bash
# AR=81 (the other order-3 multiplier mod 182 / 91) on the 120,120 groups. usage: alpha_r81.sh OUTDIR
out="$(cd "$1" && pwd)"; cd "$(dirname "$0")/../.." || exit 1
run() { tag="$1"; seed="$2"; shift 2
  env AR=81 ORBIT="3 2 2" THREADS=1 nice -n 5 timeout 1320 ./haar_sym 8 8 1200 "$seed" 8 "$out/$tag.txt" "$@" > "$out/$tag.log" 2>&1; }
run d8D8_psl_11_182_AR81_s7 7 psl 11 182 &
run d8D8_psl_11_182_AR81_s8 8 psl 11 182 &
run d8D8_sl_11_91_AR81_s7 7 sl 11 91 &
run d8D8_pgl_11_91_AR81_s7 7 pgl 11 91 &
wait; echo "alpha_r81 done"
