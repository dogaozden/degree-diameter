#!/bin/bash
# c8 proxy: RANDORB cost statistics on (15,8) sl 59 x Z_43 (mu 23), no lock.
# usage: run_proxy.sh M "ENV=.. ENV=.." ...   (each arg = one config, env assignments separated by spaces)
M=$1; shift
cd /home/user/degree-diameter/research/lowmem
for cfg in "$@"; do
  out=$(timeout 120 nice -n 10 env RANDORB=$M $cfg ./haar_lean 15 8 60 1 8 /dev/null sl 59 43 2>&1 | grep -E "^RANDORB|^ORBIT|^alpha" | tr '\n' ' ')
  echo "[$cfg] $out"
done
