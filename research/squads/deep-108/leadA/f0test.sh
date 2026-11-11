#!/bin/bash
# f0test.sh: for each good psl 23 97 state, replace the fixed letter e by each alpha-fixed element (F0=i) and print
# the plain cost of the new set (haar_sym2 EXDESC start cost; the run is cut after the first line).
H=../../../d10D8/sym2/haar_sym2
declare -A FL
for i in $(seq 1 11); do FL[$i]=$(ORBIT="3 3 1" F0=$i RANDORB=1 timeout 60 $H 10 8 10 1 1 /dev/null psl 23 97 2>&1 | sed -n 's/.*fixed letter \([0-9]*\) instead.*/\1/p'); done
grep -v '^#' good_states.tsv | awk -F'\t' '$2=="psl 23 97"' | head -${1:-6} | while IFS=$'\t' read e g src S; do
  set -- $S; rest="${@:2}"
  printf "CKPT d=10 evals=0 elapsed=0 best=0\n%s\n" "$S" > t.ckpt
  base=$(ORBIT="3 3 1" CKPT=t.ckpt EXDESC=1 timeout -s KILL 12 $H 10 8 5 1 1 /dev/null psl 23 97 2>&1 | sed -n 's/EXDESC 1 start cost //p' | head -1)
  line="E$e base $base F0:"
  for i in $(seq 1 11); do
    printf "CKPT d=10 evals=0 elapsed=0 best=0\n%s %s\n" "${FL[$i]}" "$rest" > t.ckpt
    c=$(ORBIT="3 3 1" F0=$i CKPT=t.ckpt EXDESC=1 timeout -s KILL 12 $H 10 8 5 1 1 /dev/null psl 23 97 2>&1 | sed -n 's/EXDESC 1 start cost //p' | head -1)
    line="$line $c"
  done
  echo "$line"
done
