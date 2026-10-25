#!/bin/bash
# control.sh: symmetry alone (no search). Random C-invariant designs from symbase.py, evaluated only (SECS=0) on the
# orbit sources; a design counts as VALID here only if the orbit-source count is 0 and baselift eval (all sources) agrees.
# usage: control.sh Q GROUP_JSON "m1 m2 ..." NSEED
set -u
T=/home/user/degree-diameter/research/d16D8
D=/home/user/degree-diameter/research/squads/d16D8-r3/c6
Q=$1; G=$2; MS=$3; NSEED=$4
OUT=$D/control_q$Q.txt
: > "$OUT"
for m in $MS; do
  for s in $(seq 1 "$NSEED"); do
    B=$D/ctl_q${Q}_m${m}_s${s}.base
    python3 "$T/symbase.py" gq "$Q" "$G" "$m" "$s" "$B" "$D/ctl_q${Q}.src" > /dev/null
    r=$(env THREADS=1 SRCFILE="$D/q$Q.src" "$T/symrepair" "$B" 6 0 1 /dev/null | sed 's/.*uncovered=\([0-9]*\).*/\1/')
    echo "q=$Q m=$m seed=$s orbit-uncovered=$r" >> "$OUT"
  done
done
cat "$OUT"
