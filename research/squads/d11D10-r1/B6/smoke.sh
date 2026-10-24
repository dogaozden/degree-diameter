#!/bin/bash
# B6 smoke test: deterministic short runs (VCLOCK + MAXSTEPS), one gated process at a time.
G=/home/user/degree-diameter/research/squads/d11D10-r1/gate.sh
B=/home/user/degree-diameter/research/structured/haar_sym
V=/home/user/degree-diameter/research/squads/d11D10-r1/B6/haar_sym_b6
W=/home/user/degree-diameter/research/squads/d11D10-r1/B6
cd "$W" || exit 1
run() {  # run TAG BIN [VAR=val ...]
  local tag=$1 bin=$2; shift 2
  $G 240 env ORBIT="5 2 1" ORBW=5 VCLOCK=0.01 MAXSTEPS=150 "$@" "$bin" 11 8 120 1 8 "$W/test_d11D8_psl_59_11_orb5_$tag.txt" psl 59 11 > "$W/smoke_$tag.log" 2>&1
  echo "$(date +%T) $tag rc=$?" >> "$W/smoke_status.log"
}
run base "$B"
run mt0 "$V"
run mt3 "$V" MT=3
run mt4 "$V" MT=4
echo "$(date +%T) done" >> "$W/smoke_status.log"
