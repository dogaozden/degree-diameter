#!/bin/bash
# usage: sweep.sh "ORBIT" d D GROUP... n   (prints index, |Fix|, min over RANDORB samples)
B=/tmp/claude-0/-home-user-degree-diameter/2744c2da-0db8-5a6f-87c3-01a128c9c95e/scratchpad/bin
ORB="$1"; shift; d=$1; D=$2; shift 2
SAMP=${SAMP:-300}
Q=$(echo "$@" | awk '{print $0}')
# number of indices: probe index 0 without ALPHA set to get group order from header is hard; loop until error
for I in $(seq 0 ${MAXI:-400}); do
  out=$(ALPHA=$I ORBIT="$ORB" RANDORB=$SAMP timeout 60 nice -n 10 $B/haar_sym $d $D 1 1 8 /dev/null "$@" 2>&1)
  if echo "$out" | grep -q "ALPHA out of range"; then break; fi
  if echo "$out" | grep -q "alpha^k != 1\|not an automorphism\|no conjugation\|no orbit found\|failed"; then echo "$I SKIP"; continue; fi
  fix=$(echo "$out" | grep -o "|Fix(alpha)| = [0-9]*" | grep -o "[0-9]*$")
  mn=$(echo "$out" | grep -o "min=[0-9]*" | head -1 | cut -d= -f2)
  p1=$(echo "$out" | grep -o "p1=[0-9]*" | head -1 | cut -d= -f2)
  echo "$I fix=$fix min=$mn p1=$p1"
done
