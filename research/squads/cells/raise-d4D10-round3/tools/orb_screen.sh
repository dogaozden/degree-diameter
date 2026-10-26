#!/bin/bash
# usage: orb_screen.sh "ORBIT-config" "N|spec"   -> one TSV line
CFG="$1"; LINE="$2"; BIN=/tmp/claude-0/-home-user-degree-diameter/d68c5ced-3930-535c-a641-3fa3cd4e68f4/scratchpad/bin/haar_sym
N="${LINE%%|*}"; SPEC="${LINE#*|}"
OUT=$(ORBIT="$CFG" RANDORB=${RANDORB:-20000} THREADS=1 timeout 120 nice $BIN 4 10 1 1 1 /dev/null $SPEC 2>&1)
R=$(echo "$OUT" | grep '^RANDORB d=' | head -1)
if [ -z "$R" ]; then E=$(echo "$OUT" | grep -iE 'error|needs|not|no orbit|fail|usage|alpha' | head -1 | tr '\t' ' '); printf "%s\t%s\tERR\t%s\n" "$N" "$SPEC" "$E"; exit 0; fi
MIN=$(echo "$R" | grep -o 'min=[0-9]*' | cut -d= -f2); P10=$(echo "$R" | grep -o 'p10=[0-9]*' | cut -d= -f2); MED=$(echo "$R" | grep -o 'median=[0-9]*' | cut -d= -f2)
printf "%s\t%s\t%s\t%s\t%s\t%s\n" "$N" "$SPEC" "$CFG" "$MIN" "$P10" "$MED"
