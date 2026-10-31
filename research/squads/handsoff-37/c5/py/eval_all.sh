#!/bin/bash
# usage: eval_all.sh DIR M  -> prints far (EVAL cost) for each state file in DIR
d=$1; m=$2
for f in $d/*.state; do
  read FA FB < <(head -1 $f)
  c=$(EVAL=1 OUTP=$f INIT=$f ./fixsa $m $FA $FB 1 1 1 1 1 /dev/null 2>/dev/null | grep EVAL | sed 's/EVAL cost=//')
  echo "$(basename $f) $c"
done
