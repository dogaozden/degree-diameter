#!/bin/bash
# RANDORB shape screen: 60 random symmetric S per group, no search. Lines: "RANDORB ..." in out/screen.log
B=/home/user/degree-diameter/research/frontier/beyond13/bin
cd /home/user/degree-diameter/research/squads/beyond13b/r1/e5
while read -r oa ob oc fam p n; do
  [ -z "$oa" ] && continue
  ord="$oa $ob $oc"
  ORBIT="$ord" RANDORB=60 $B/haar_big0 6 13 1 1 8 out/scr_${ord// /}_${fam}_${p}_${n}.sol $fam $p $n 2>>out/screen.err | grep '^RANDORB d' | sed "s/^/k=$oa /"
done <<'LIST'
5 1 1 sl 89 31
5 1 1 sl 71 61
5 1 1 psl 89 61
5 1 1 psl 71 121
5 1 1 psl 61 187
5 1 1 psl 59 205
5 1 1 psl 109 33
5 1 1 psl 101 41
5 1 1 sl 41 311
5 1 1 sl 61 93
5 1 1 psl 349 1
5 1 1 sl 41 305
5 1 1 psl 61 191
5 1 1 psl 59 209
5 1 1 psl 59 211
5 1 1 sl 41 319
5 1 1 sl 281 1
3 2 0 sl 89 31
3 2 0 sl 71 61
3 2 0 psl 89 61
3 2 0 psl 71 121
3 2 0 psl 61 187
3 2 0 psl 59 205
3 2 0 psl 109 33
3 2 0 psl 101 41
3 2 0 sl 41 311
3 2 0 sl 61 93
3 2 0 psl 349 1
3 2 0 sl 41 305
3 2 0 psl 61 191
3 2 0 psl 59 209
3 2 0 psl 59 211
3 2 0 sl 41 319
3 2 0 sl 281 1
3 2 0 psl 83 73
LIST
echo "SCREEN DONE $(date -u +%T)"
