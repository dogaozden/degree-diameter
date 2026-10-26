#!/bin/bash
# run.sh TAG BASE... -- GROUP... : flift 10 s, seed 1, d=6 D=5, one line per (base, group) appended to log_TAG.txt
cd "$(dirname "$0")"; export OMP_NUM_THREADS=1 THREADS=1
tag=$1; shift; bases=(); groups=()
while [ "$1" != "--" ]; do bases+=("$1"); shift; done; shift; groups=("$@")
mkdir -p out
for b in "${bases[@]}"; do for g in "${groups[@]}"; do
  o=out/$tag.$b.$(echo $g | tr ':' '_')
  r=$(timeout 25 nice -n 10 ../../tools/flift bases/$b.txt $g 6 5 10 1 8 $o.sol | grep RESULT)
  echo "$b $g :: $r" >> log_$tag.txt
done; done
echo DONE >> log_$tag.txt
