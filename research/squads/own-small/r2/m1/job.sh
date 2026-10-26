#!/bin/bash
# Card r2-m1 (3,9), D=9: joint base+voltage annealing (salift_s2), p=5 N=51,52 (n=510,520), p=6 N=43,44 (n=516,528).
# Phase 1: screen every group (non-abelian first), 30 CPU s each, seed 1.
# Phase 2: restart the 4 best screened states from their .best with fresh seeds, 100 CPU s each.
# Phase 3: one more restart of the overall best state, 100 CPU s.
# Every cost-0 state is converted with best2edges.py and checked with score48 at once.
T=/home/user/degree-diameter/research/squads/own-small/tools
GT=/home/user/degree-diameter/research/squads/own-small/runs/gtxt
W=/home/user/degree-diameter/research/squads/own-small/r2/m1
export D=9
cd $W || exit 1
mkdir -p screen push valid
LOG=$W/job.log
say() { echo "$(date -u +%T) $*" >> $LOG; }
say "job start"

# order: non-abelian groups first (flag 0 in groups_all.txt), then abelian (flag 1)
awk '$4==0' groups_all.txt > order.txt; awk '$4==1' groups_all.txt >> order.txt
say "order: $(wc -l < order.txt) groups"

check() {  # check SOL N TAG: convert a cost-0 state and score it with score48
  local sol=$1 N=$2 tag=$3
  python3 -I $T/best2edges.py $GT/g$N.txt $sol valid/$tag.edges > /dev/null 2>&1
  local res; res=$($T/bin/score48 valid/$tag.edges 3 9 2>&1 | tail -1)
  say "CHECK $tag n=$(tagn $tag) $res"
}
tagn() { local p N; p=$(echo $1 | sed 's/p\([0-9]*\)_N.*/\1/'); N=$(echo $1 | sed 's/.*_N\([0-9]*\)_g.*/\1/'); echo $((2*p*N)); }

# Phase 1: screen
while read p N id ab; do
  tag=p${p}_N${N}_g${id}
  $T/bin/salift_s2 $p $GT/g$N.txt $id 1 30 10 0.3 screen/$tag.sol < /dev/null > screen/$tag.log 2>&1
  say "screen $tag $(tail -1 screen/$tag.log) | $(grep -c FOUND screen/$tag.log) found"
  if [ -f screen/$tag.sol ]; then check screen/$tag.sol $N $tag; fi
done < order.txt

# ranking of screened states by cost (from the .best header "N id p cost")
rank() {
  while read p N id ab; do
    tag=p${p}_N${N}_g${id}
    [ -f screen/$tag.sol ] && { echo "0 $tag $N"; continue; }
    [ -f screen/$tag.sol.best ] && echo "$(head -1 screen/$tag.sol.best | awk '{print $4}') $tag $N"
  done < order.txt | sort -n -k1,1 -s
}
rank > screen_rank.txt
say "screen ranking: $(head -4 screen_rank.txt | tr '\n' ' ')"

# Phase 2: restart the best 4 screened states (fresh seeds)
seed=10
for entry in $(head -4 screen_rank.txt | awk '{print $2}'); do
  [ -f screen/$entry.sol ] && continue   # already valid, handled above
  p=$(echo $entry | sed 's/p\([0-9]*\)_N.*/\1/'); N=$(echo $entry | sed 's/.*_N\([0-9]*\)_g.*/\1/'); id=$(echo $entry | sed 's/.*_g//')
  seed=$((seed+1)); tag=${entry}_s$seed
  START=screen/$entry.sol.best $T/bin/salift_s2 $p $GT/g$N.txt $id $seed 100 10 0.3 push/$tag.sol < /dev/null > push/$tag.log 2>&1
  say "push $tag $(tail -1 push/$tag.log) | $(grep -c FOUND push/$tag.log) found"
  if [ -f push/$tag.sol ]; then check push/$tag.sol $N $tag; fi
done

# Phase 3: restart the overall best non-valid state once more
best=$(for f in push/*.sol.best screen/*.sol.best; do [ -f "$f" ] && echo "$(head -1 $f | awk '{print $4}') $f"; done | awk '$1>0' | sort -n -k1,1 | head -1 | awk '{print $2}')
if [ -n "$best" ]; then
  base=$(basename $best .sol.best); p=$(echo $base | sed 's/p\([0-9]*\)_N.*/\1/'); N=$(echo $base | sed 's/.*_N\([0-9]*\)_g.*/\1/'); id=$(echo $base | sed 's/.*_g\([0-9]*\).*/\1/')
  seed=99; tag=final_${base}
  START=$best $T/bin/salift_s2 $p $GT/g$N.txt $id $seed 100 3 0.3 push/$tag.sol < /dev/null > push/$tag.log 2>&1
  say "final $tag from $best: $(tail -1 push/$tag.log) | $(grep -c FOUND push/$tag.log) found"
  if [ -f push/$tag.sol ]; then check push/$tag.sol $N $tag; fi
fi
say "job end"
