#!/bin/bash
# k7 (3,10), p=8, N=51..56 (n=16N): screen every group (15 CPU s, seed 1), then START restarts of the best
# non-valid state at the highest N above the best valid order. Cost-0 states are converted and checked at once.
T=/home/user/degree-diameter/research/squads/own-small/tools
GT=/home/user/degree-diameter/research/squads/own-small/runs/gtxt
W=/home/user/degree-diameter/research/squads/own-small/r2/k7
P=8; SCREEN=15; RS=90
export D=10
cd $W || exit 1
DL=$(( $(date +%s) + 830 ))
LOG=$W/job.log; SUM=$W/screen.tsv
: > $SUM
MAXV=0; BESTVALID=""
echo "start $(date -u +%T)" >> $LOG

check() {  # $1 = state file (header "N id p cost"), $2 = tag
  local st=$1 tag=$2 N id p cost
  read N id p cost < "$st"
  if [ "$cost" = "0" ]; then
    python3 -I $T/best2edges.py $GT/g$N.txt "$st" $W/$tag.edges >> $LOG 2>&1
    local res=$($T/bin/score48 $W/$tag.edges 3 10 | grep RESULT | tail -1)
    echo "CHECK $tag N=$N id=$id : $res" >> $LOG
    if echo "$res" | grep -q "RESULT VALID"; then
      local nn=$(echo "$res" | sed -n 's/.*n=\([0-9]*\).*/\1/p')
      cp $W/$tag.edges $W/VALID_n${nn}_N${N}_g${id}.edges
      cp "$st" $W/VALID_n${nn}_N${N}_g${id}.state
      [ "$N" -gt "$MAXV" ] && MAXV=$N && BESTVALID="n=$nn N=$N id=$id ($tag)"
    fi
  fi
}

# 1) screen all groups, ascending order
for N in 51 52 53 54 55 56; do
  for id in $(grep "^G $N " $GT/g$N.txt | awk '{print $3}'); do
    now=$(date +%s); [ $((now + SCREEN + 3)) -gt $DL ] && continue
    tag=s_${N}_${id}_1
    $T/bin/salift_s2 $P $GT/g$N.txt $id 1 $SCREEN 10 0.3 $W/$tag.sol > $W/$tag.log 2>&1
    st=$W/$tag.sol.best
    [ -f "$st" ] || { echo "$N $id NA" >> $SUM; continue; }
    read a b c cost < "$st"
    echo "$N $id $cost" >> $SUM
    echo "screen N=$N id=$id cost=$cost $(date -u +%T)" >> $LOG
    check "$st" $tag
  done
done

# 2) START restarts: best cost>0 state at the largest N above the best valid order (tie: lower cost)
round=0
while true; do
  now=$(date +%s); rem=$((DL - now))
  [ $rem -lt 40 ] && break
  rs=$RS; [ $rs -gt $((rem - 5)) ] && rs=$((rem - 5))
  sel=$(for f in $W/*.sol.best; do
          [ -f "$f" ] || continue
          read N id p cost < "$f"
          [ "$cost" -gt 0 ] 2>/dev/null && [ "$N" -gt "$MAXV" ] && echo "$cost $N $id $f"
        done | sort -k1,1n -k2,2nr | head -1)
  [ -z "$sel" ] && break
  set -- $sel; cst=$1; N=$2; id=$3; sf=$4
  round=$((round+1)); seed=$((100+round))
  tag=r_${N}_${id}_${seed}
  START=$sf $T/bin/salift_s2 $P $GT/g$N.txt $id $seed $rs 10 0.3 $W/$tag.sol > $W/$tag.log 2>&1
  echo "restart round=$round N=$N id=$id from cost=$cst seed=$seed $(date -u +%T)" >> $LOG
  [ -f $W/$tag.sol.best ] && check $W/$tag.sol.best $tag
  [ -f $W/$tag.sol.best ] && read a b c rc < $W/$tag.sol.best && echo "$N $id $rc $tag" >> $SUM
done

echo "end $(date -u +%T) maxvalid_N=$MAXV best=[$BESTVALID]" >> $LOG
