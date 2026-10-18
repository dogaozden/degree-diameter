#!/bin/bash
cd /Users/dogaozden/AI_Projects/degree-diameter/research/gq4
for cap in 30 60 150 300; do
  /usr/bin/python3 sym_spread.py 9 40 20 $((cap+7)) 4 $cap > runs_sym/q9_cap${cap}.log 2>&1
done
echo CHAIN_DONE >> runs_sym/q9_cap300.log
