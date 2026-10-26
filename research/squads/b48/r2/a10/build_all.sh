#!/bin/bash
# name p f k d
cd /home/user/degree-diameter/research/squads/b48/r2/a10
while read name p f k d; do
  [ -z "$name" ] && continue
  timeout 120 nice -n 10 python3 fgroup.py $p $f $k $d groups/$name.bin >/dev/null || echo "FAIL $name"
done <<'LIST'
f8_k140_d7 2 3 140 7
f8_k147_d7 2 3 147 7
f8_k154_d7 2 3 154 7
f9_k128_d8 3 2 128 8
f9_k136_d8 3 2 136 8
f9_k124_d4 3 2 124 4
f9_k132_d4 3 2 132 4
f9_k132_d2 3 2 132 2
f16_k70_d5 2 4 70 5
f16_k75_d15 2 4 75 15
f16_k72_d3 2 4 72 3
f25_k45_d3 5 2 45 3
f25_k48_d6 5 2 48 6
f25_k48_d8 5 2 48 8
f25_k48_d24 5 2 48 24
f25_k48_d12 5 2 48 12
f25_k44_d2 5 2 44 2
f27_k42_d2 3 3 42 2
f49_k24_d24 7 2 24 24
f49_k24_d12 7 2 24 12
f49_k24_d8 7 2 24 8
f49_k24_d4 7 2 24 4
f64_k18_d9 2 6 18 9
f81_k15_d5 3 4 15 5
f121_k10_d10 11 2 10 10
f121_k10_d5 11 2 10 5
f125_k10_d2 5 3 10 2
f169_k7_d7 13 2 7 7
pm11_k110_d10 11 1 110 10
pm13_k96_d12 13 1 96 12
pm31_k40_d10 31 1 40 10
pm37_k33_d3 37 1 33 3
LIST
