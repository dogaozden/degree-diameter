#!/bin/bash
# B4 driver: RANDORB=3 LEVELS=3 ball-growth census of 18 (group, n, orbit) cells, one gated run at a time.
D=/home/user/degree-diameter/research/squads/d11D10-r1
B=$D/B4
cd "$B" || exit 1
run() {  # run ORBIT FAM P N
  local orb="$1" fam="$2" p="$3" n="$4" k
  k=$(echo "$orb" | cut -d' ' -f1)
  local tag="${fam}_${p}_${n}_orb${k}"
  echo "$(date -u +%T) start $tag" >> "$B/driver.log"
  "$D/gate.sh" 121 bash "$B/one.sh" "$orb" "$fam" "$p" "$n" "$B/randorb_$tag.log"
  local rc=$?
  echo "$(date -u +%T) done $tag gate_rc=$rc" >> "$B/driver.log"
}
for spec in "psl 41 2161" "psl 61 661" "psl 41 2201" "psl 89 211" "psl 71 421" "psl 79 311" \
            "sl 61 331" "sl 41 1091" "sl 71 211" "psl 101 151" "psl 59 761" "psl 109 121"; do
  set -- $spec
  run "5 2 1" "$1" "$2" "$3"
done
for spec in "psl 61 661" "psl 71 421" "psl 127 73" "sl 61 331" "sl 73 193" "sl 101 73"; do
  set -- $spec
  run "3 3 2" "$1" "$2" "$3"
done
echo "$(date -u +%T) all done" >> "$B/driver.log"
