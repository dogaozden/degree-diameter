#!/bin/bash
# B6 batch, run inside ONE gate slot call: 4 short deterministic smoke runs (VCLOCK + MAXSTEPS), then 3 seeds x {base, MT=3} at 60 s.
B=/home/user/degree-diameter/research/structured/haar_sym
V=/home/user/degree-diameter/research/squads/d11D10-r1/B6/haar_sym_b6
W=/home/user/degree-diameter/research/squads/d11D10-r1/B6
ST=$W/smoke_status.log
cd "$W" || exit 1
echo "$(date +%T) batch start" >> "$ST"
smoke() {  # smoke TAG BIN [VAR=val ...]
  local tag=$1 bin=$2; shift 2
  env ORBIT="5 2 1" ORBW=5 VCLOCK=0.01 MAXSTEPS=150 "$@" "$bin" 11 8 120 1 8 "$W/test_d11D8_smoke_$tag.txt" psl 59 11 > "$W/smoke_$tag.log" 2>&1
  echo "$(date +%T) smoke $tag rc=$?" >> "$ST"
}
smoke base "$B"
smoke mt0 "$V"
smoke mt3 "$V" MT=3
smoke mt4 "$V" MT=4
for s in 1 2 3; do
  env ORBIT="5 2 1" ORBW=5 "$B" 11 8 60 "$s" 8 "$W/test_d11D8_base_s$s.txt" psl 59 11 > "$W/cmp_base_s$s.log" 2>&1
  echo "$(date +%T) cmp base s$s rc=$?" >> "$ST"
  env ORBIT="5 2 1" ORBW=5 MT=3 "$V" 11 8 60 "$s" 8 "$W/test_d11D8_mt3_s$s.txt" psl 59 11 > "$W/cmp_mt3_s$s.log" 2>&1
  echo "$(date +%T) cmp mt3 s$s rc=$?" >> "$ST"
done
echo "$(date +%T) batch done" >> "$ST"
