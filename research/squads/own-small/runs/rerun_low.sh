#!/bin/bash
# Exact cost <= LIM assignments for the groups whose LIMIT=0 lower bound was <= LIM in a scan22 tsv (2+2 base, D).
# Usage: rerun_low.sh SCAN.tsv D LIM OUT
cd /home/user/degree-diameter/research/squads/own-small
S=$1; D=$2; LIM=$3; OUT=$4; G=/tmp/claude-0/-home-user-degree-diameter/6bbfb942-4016-5a09-834c-7684c0cc81b5/scratchpad/groups
awk -F'\t' -v L=$LIM '$3!=""{split($2,a," "); split($3,b," "); if (b[4] <= L) print $1, a[1]}' $S | while read N id; do
  f=$(printf "%s/b%d/g%d_%04d" $G $N $N $id)
  [ -f $f.bin ] || python3 tools/split_groups.py $G/t$N.txt $G/b$N
  m=$(tools/bin/gen22 < $f.reps | LIMIT=$LIM ONLYLOW=1 tools/bin/flift tools/bases/cubic/b22_cubic.txt $f.bin 3 $D eval 2>&1 > $f.D$D.L$LIM | tail -1)
  echo -e "$N\t$id\t$m\t$(sort -n $f.D$D.L$LIM | head -1)" >> $OUT
done
echo DONE >> $OUT
