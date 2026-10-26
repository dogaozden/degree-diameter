#!/bin/bash
# Card k11, cell (3,10), D=10. Screen p=5 over N=100,99,98,97,96 (n=1000..960) and p=6 over N=82,83,84 (n=984..1008),
# 20 CPU s per (group, seed 1); then push the best 4 non-zero states with START restarts (70 s each).
# Every cost-0 state is converted with best2edges.py and checked with score48 3 10 at once.
T=/home/user/degree-diameter/research/squads/own-small/tools
GT=/home/user/degree-diameter/research/squads/own-small/runs/gtxt
W=/home/user/degree-diameter/research/squads/own-small/r2/k11
cd $W || exit 1
mkdir -p out
export D=10
SC=out/screen.tsv; : > $SC
CK=out/checks.txt; : > $CK
LAST=999999

one() { # tag p N id seed secs T0 T1 [startfile]
  local tag=$1 p=$2 N=$3 id=$4 seed=$5 secs=$6 t0=$7 t1=$8 st=$9
  local o=out/$tag.sol
  rm -f $o $o.best out/$tag.log
  if [ -n "$st" ]; then export START=$st; else unset START; fi
  timeout $((secs+40)) $T/bin/salift_s2 $p $GT/g$N.txt $id $seed $secs $t0 $t1 $o > out/$tag.log 2>&1
  unset START
  LAST=$(grep -o 'end best [0-9]*' out/$tag.log | awk '{print $3}')
  [ -z "$LAST" ] && LAST=$(grep -o 'best [0-9]*' out/$tag.log | tail -1 | awk '{print $2}')
  [ -z "$LAST" ] && LAST=999999
  if [ -f $o ]; then
    python3 -I $T/best2edges.py $GT/g$N.txt $o out/$tag.edges > /dev/null 2>&1
    R=$($T/bin/score48 out/$tag.edges 3 10 2>&1 | grep RESULT | tail -1)
    echo "$tag n=$((2*p*N)) $R" >> $CK
  fi
}

screen() { # p N ids...
  local p=$1 N=$2; shift 2
  for id in "$@"; do
    local tag=s_p${p}_N${N}_g${id}
    one $tag $p $N $id 1 20 6 0.3 ""
    echo -e "$LAST\t$tag\t$p\t$N\t$id" >> $SC
  done
}

screen 5 100 2 4 7 8 13 16
screen 5 99 1 2
screen 5 98 2 4
screen 5 97 1
screen 5 96 3 9 13 17 26 33 45 58
screen 6 82 1 2
screen 6 83 1
screen 6 84 1 11

# push: best 4 non-zero states from the screen (cost, then larger N first)
awk -F'\t' '$1>0' $SC | sort -t$'\t' -k1,1n -k4,4nr | head -4 > out/top.tsv
j=0
while IFS=$'\t' read -r c tag p N id; do
  j=$((j+1))
  st=out/$tag.sol.best
  [ -f $st ] || continue
  one push${j}_$tag $p $N $id $((200+j)) 70 4 0.3 $st
  echo -e "$LAST\tpush${j}_$tag\t$p\t$N\t$id" >> out/push.tsv
done < out/top.tsv
echo JOBDONE >> $CK
