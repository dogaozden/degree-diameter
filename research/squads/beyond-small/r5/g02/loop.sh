#!/bin/bash
# Repeat step.sh until 2900 s have passed (time box 50 min).
cd "$(dirname "$0")"
t0=$(date +%s)
while [ $(( $(date +%s) - t0 )) -lt 2900 ]; do
  ./step.sh >> loop_g02.out 2>&1
done
echo DONE >> loop_g02.out
