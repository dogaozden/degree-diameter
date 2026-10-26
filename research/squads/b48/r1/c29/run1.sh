#!/bin/bash
# c29 round 1: Cayley graphs of involution-generated groups (bouquet_4semi), 12 s lift anneal each
T=/home/user/degree-diameter/research/squads/b48/tools
D=/home/user/degree-diameter/research/squads/b48/r1/c29
i=0
while IFS='|' read -r tag spec; do
  [ -z "$tag" ] && continue
  i=$((i+1))
  f=$D/g_$tag.bin
  THREADS=1 timeout 120 nice -n 10 python3 $T/groups.py "$spec" $f > $D/build_$tag.log 2>&1 || { echo "BUILD FAIL $tag"; continue; }
  head -c 300 $D/build_$tag.log | tr '\n' ' '; echo
  THREADS=1 timeout 120 nice -n 10 $T/lift $T/bases/bouquet_4semi.txt $f 4 8 12 $i 8 $D/sol_$tag QUIET=1 2>&1 | grep RESULT | sed "s/^/$tag /"
  rm -f $f
done <<'LIST'
S4xD46|perm 4 1,0,2,3 ; 1,2,3,0 x dih 46
S4xD48|perm 4 1,0,2,3 ; 1,2,3,0 x dih 48
S4xD50|perm 4 1,0,2,3 ; 1,2,3,0 x dih 50
D24xD23|dih 24 x dih 23
D32xD18|dih 32 x dih 18
PSL27xD7|psl2 7 x dih 7
D6xD7xD7|dih 6 x dih 7 x dih 7
S3S3D32|perm 3 1,0,2 ; 1,2,0 x perm 3 1,0,2 ; 1,2,0 x dih 32
S5xD10|perm 5 1,0,2,3,4 ; 1,2,3,4,0 x dih 10
S4S3D8|perm 4 1,0,2,3 ; 1,2,3,0 x perm 3 1,0,2 ; 1,2,0 x dih 8
LIST
