#!/bin/bash
# usage: screen.sh SECS  -- runs every combo x base, 2 at a time
cd /home/user/degree-diameter/research/squads/f65r1/c3
SECS=$1
run_one(){ # tag base group...
  tag=$1; base=$2; shift 2
  b=$(basename $base .txt)
  timeout 600 nice -n 10 ./lift search $base 5 $SECS 1 8 runs/${tag}_${b}.sol "$@" > runs/${tag}_${b}.log 2>&1
}
export -f run_one; export SECS
jobs=()
while read tag h grp; do
  for b in $(ls bases/h${h}_*.txt); do
    jobs+=("$tag|$b|$grp")
  done
done < combos.txt
printf '%s\n' "${jobs[@]}" | xargs -P 2 -I{} bash -c 'IFS="|" read -r t b g <<< "{}"; run_one "$t" "$b" $g'
echo DONE
