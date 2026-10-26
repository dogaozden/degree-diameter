#!/bin/bash
# Card k10 (3,10), n > 810 via prime-power groups. One gated job: screen p=4 over order 125 and p=7 over 30 order-64
# groups (d=2 first), then restart the two best states with START (two seeds), converting and scoring any cost-0 state.
T=/home/user/degree-diameter/research/squads/own-small/tools
GT=/home/user/degree-diameter/research/squads/own-small/runs/gtxt
K=/home/user/degree-diameter/research/squads/own-small/r2/k10
cd $K || exit 1
export D=10
mkdir -p scr push zero
LOG=$K/job.log
echo "job start $(date -u +%H:%M:%S)" >> $LOG

# log line "end best C its I" -> C (or 999999)
endbest() { grep -h '^end best' "$1" 2>/dev/null | tail -1 | awk '{print $3}' | grep -E '^[0-9]+$' || echo 999999; }

check_zero() {  # $1 = state file (.best or .sol), $2 = groups file, $3 = tag
  local st=$1 gr=$2 tag=$3
  [ -f "${st%.best}" ] && st=${st%.best}
  python3 -I $T/best2edges.py $gr $st $K/zero/$tag.edges > $K/zero/$tag.conv 2>&1 || { echo "conv fail $tag" >> $LOG; return; }
  $T/bin/score48 $K/zero/$tag.edges 3 10 > $K/zero/$tag.check 2>&1
  echo "CHECK $tag $(tail -1 $K/zero/$tag.check)" >> $LOG
}
mkdir -p zero

# screen A: p=4 over the 5 groups of order 125 (n=1000)
while read -r gid; do
  $T/bin/salift_s2 4 $GT/g125.txt $gid 1 25 10 0.3 scr/a125_$gid.sol > scr/a125_$gid.log 2>&1
  c=$(endbest scr/a125_$gid.log); echo "A g125 id=$gid cost=$c" >> $LOG
  if [ "$c" = 0 ]; then check_zero scr/a125_$gid.sol.best $GT/g125.txt a125_$gid; fi
done < <(seq 1 5)

# screen B: p=7 over 30 groups of order 64 (n=896), 15 CPU s each
while read -r gid d name; do
  $T/bin/salift_s2 7 $GT/g64.txt $gid 1 15 10 0.3 scr/b64_$gid.sol > scr/b64_$gid.log 2>&1
  c=$(endbest scr/b64_$gid.log); echo "B g64 id=$gid d=$d cost=$c  $name" >> $LOG
  if [ "$c" = 0 ]; then check_zero scr/b64_$gid.sol.best $GT/g64.txt b64_$gid; fi
done < <(awk '{print $1, $2, $3, $4, $5, $6}' $K/pick64.txt)

# push: the two best screened states (distinct), START restarts with two seeds, 60 CPU s each
grep -h '^ *[AB] ' $LOG | sed -E 's/.*(A|B) (g125|g64) id=([0-9]+).*cost=([0-9]+).*/\4 \2 \3 \1/' | sort -n > $K/ranked.txt
echo "ranked:" >> $LOG; head -8 $K/ranked.txt >> $LOG
top=$(head -2 $K/ranked.txt)
echo "$top" | while read -r c grp gid ab; do
  if [ "$grp" = g125 ]; then p=4; gf=$GT/g125.txt; st=scr/a125_$gid.sol.best; else p=7; gf=$GT/g64.txt; st=scr/b64_$gid.sol.best; fi
  for seed in 2 3; do
    tag=push_${grp}_${gid}_s$seed
    START=$st $T/bin/salift_s2 $p $gf $gid $seed 60 10 0.3 push/$tag.sol > push/$tag.log 2>&1
    pc=$(endbest push/$tag.log); echo "PUSH $tag start_cost=$c end=$pc" >> $LOG
    if [ "$pc" = 0 ]; then check_zero push/$tag.sol.best $gf $tag; fi
    if [ -f push/$tag.sol ]; then check_zero push/$tag.sol $gf $tag; fi
  done
done
echo "job end $(date -u +%H:%M:%S)" >> $LOG
