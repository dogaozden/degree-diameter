#!/bin/bash
# usage: sieve12.sh TYPE SECS RANDCOMB DEADLINE_EPOCH GROUP...   (GROUP like 348_6 = SmallGroup(348,6))
# Same as scan12.sh but for an explicit list of groups. Results appended to scan/sieve_<TAG>.tsv
T=$1; S=$2; RC=$3; DL=$4; shift 4
D=/home/user/degree-diameter/research/squads/handsoff-65
G=$D/c5/groups
W=$D/c12
cd "$W/scan" || exit 1
TAG=$(echo "$T" | tr '|,' '_-')
OUT=$W/scan/sieve.tsv
touch "$OUT"
for g in "$@"; do
  b=sg_$g
  f=$G/$b.txt
  [ -f "$f" ] || continue
  [ "$(date +%s)" -ge "$DL" ] && exit 0
  grep -q "^$T	$b	" "$OUT" 2>/dev/null && continue
  LOG=$W/scan/sv.$TAG.$b.log
  timeout $((S*RC+60)) env TYPE="$T" SECS=$S SEED=1 RANDCOMB=$RC EDGES="$W/scan/sv.$TAG.$b.best.edges" nice -n 10 $D/shared/mcos "$f" > "$LOG" 2>&1
  best=$(grep "^RESULT" "$LOG" | awk '{print $3}')
  [ -z "$best" ] && best=ERR
  printf '%s\t%s\t%s\t%s\n' "$T" "$b" "$(head -c 30 $G/$b.name | tr -d '\t')" "$best" >> "$OUT"
  [ "$best" = "0" ] && echo "HIT $b $T" >> "$OUT"
done
