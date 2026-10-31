#!/bin/bash
# usage (from c5/): deep.sh TYPE SECS RANDCOMB GROUP_BASENAME...   (e.g. sg_348_6)
# Longer mcos runs on named groups; results to deep/<TAG>.tsv and logs deep/<TAG>.<group>.<SECS>.log
T=$1; S=$2; RC=$3; shift 3
cd "$(dirname "$0")" || exit 1
TAG=$(echo "$T" | tr '|,' '_-'); mkdir -p deep
for b in "$@"; do
  f=groups/$b.txt; [ -f "$f" ] || { echo "missing $f"; continue; }
  L=deep/$TAG.$b.s$S.log
  timeout 900 env TYPE="$T" SECS=$S SEED=7 RANDCOMB=$RC EDGES="deep/$TAG.$b.best.edges" nice -n 10 ../shared/mcos "$f" > "$L" 2>&1
  best=$(grep "^RESULT" "$L" | awk '{print $3}')
  printf '%s\t%s\t%s\t%s\t%s\n' "$b" "$(head -c 40 groups/$b.name)" "$T" "S=$S" "$best" >> deep/$TAG.tsv
done
