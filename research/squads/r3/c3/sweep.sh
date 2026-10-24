#!/bin/bash
# usage: sweep.sh OUTFILE AR GROUP... (group spec includes n as last token)
B=/tmp/claude-0/-home-user-degree-diameter/2744c2da-0db8-5a6f-87c3-01a128c9c95e/scratchpad/bin
OUT=$1; AR=$2; shift 2
GROUP="$*"
IDX_LIST=${IDX_LIST:-$(seq 0 2183)}
: > "$OUT"
for I in $IDX_LIST; do
  if [ -n "$AR" ]; then
    out=$(ALPHA=$I AR=$AR ORBIT="3 3 1" RANDORB=20000 timeout 120 nice -n 10 $B/haar_sym 10 5 1 1 8 /dev/null $GROUP 2>&1)
  else
    out=$(ALPHA=$I ORBIT="3 3 1" RANDORB=20000 timeout 120 nice -n 10 $B/haar_sym 10 5 1 1 8 /dev/null $GROUP 2>&1)
  fi
  if echo "$out" | grep -q "alpha^k != 1"; then echo "$I SKIP_ORDER" >> "$OUT"; continue; fi
  fix=$(echo "$out" | grep -o "|Fix(alpha)| = [0-9]*" | grep -o "[0-9]*$" | head -1)
  mn=$(echo "$out" | grep -o "min=[0-9]*" | head -1 | cut -d= -f2)
  p1=$(echo "$out" | grep -o "p1=[0-9]*" | head -1 | cut -d= -f2)
  al=$(echo "$out" | grep -o "alpha: conj by [^,]*" | head -1)
  if [ -z "$fix" ] || [ -z "$mn" ]; then echo "$I FAIL" >> "$OUT"; continue; fi
  echo "$I fix=$fix min=$mn p1=$p1 $al" >> "$OUT"
done
