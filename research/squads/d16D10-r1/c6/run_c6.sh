#!/bin/bash
# c6 (wildcard groups) at the proxy (d,D)=(16,8), ORBIT="3 5 1", default recipe K=8, 90 s budget per run (same as the
# preamble reference), THREADS=1, two streams (at most 2 runs at a time), every run under timeout + nice.
T=/tmp/claude-0/-home-user-degree-diameter/4ce63409-b0f8-5c33-8f23-00173ad34031/scratchpad/tools/research/structured
C=/home/user/degree-diameter/research/squads/d16D10-r1/c6
L=$C/logs
mkdir -p $L
run() {  # tag seed GROUP... n
  local tag=$1 seed=$2; shift 2
  env ORBIT="3 5 1" THREADS=1 timeout 200 nice -n 10 $T/haar_sym 16 8 90 $seed 8 /dev/null "$@" > $L/$tag.out 2> $L/$tag.err
  echo "$tag exit=$?" >> $L/done.txt
}
( run psl49_z229_s1 1 psl 49 229
  run psl49_z229_s2 2 psl 49 229
  run sl8xsl9_z37_s1 1 prod sl 8 sl 9 37
  run sl8xsl9_z37_s2 2 prod sl 8 sl 9 37
  run sl5xsl9_z157_s1 1 prod sl 5 sl 9 157 ) &
( run psl7xpsl9_z223_s1 1 prod psl 7 psl 9 223
  run psl7xpsl9_z223_s2 2 prod psl 7 psl 9 223
  run psl25_z1729_s1 1 psl 25 1729
  run psl25_z1729_s2 2 psl 25 1729
  run sl5xsl9_z157_s2 2 prod sl 5 sl 9 157 ) &
wait
echo ALLDONE >> $L/done.txt
