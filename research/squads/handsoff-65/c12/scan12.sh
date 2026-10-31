#!/bin/bash
# usage: scan12.sh TYPE SECS RANDCOMB DEADLINE_EPOCH ORDER...
# Runs shared/mcos with TYPE on every non-abelian group table (from c5/groups, read only) of the given orders,
# skipping groups already logged for this TYPE. Stops starting new runs after DEADLINE_EPOCH.
# Appends "order<TAB>group<TAB>name<TAB>type<TAB>best" to scan/<TAG>.tsv. Cost-0 hits are marked HIT.
T=$1; S=$2; RC=$3; DL=$4; shift 4
D=/home/user/degree-diameter/research/squads/handsoff-65
G=${GDIR:-$D/c5/groups}
W=$D/c12
cd "$W/scan" || exit 1
TAG=$(echo "$T" | tr '|,' '_-')
OUT=$W/scan/$TAG.tsv
touch "$OUT"
for N in "$@"; do
  for f in $G/sg_${N}_*.txt; do
    b=$(basename "$f" .txt)
    [ -f $G/$b.name ] || continue
    grep -q "abelian=true" $G/$b.name && continue
    [ "$(date +%s)" -ge "$DL" ] && exit 0
    grep -q "^$N	$b	" "$OUT" 2>/dev/null && continue
    LOG=$W/scan/$TAG.$b.log
    timeout $((S*RC+60)) env TYPE="$T" SECS=$S SEED=1 RANDCOMB=$RC EDGES="$W/scan/$TAG.$b.best.edges" nice -n 10 ${BIN:-$D/shared/mcos} "$f" > "$LOG" 2>&1
    best=$(grep "^RESULT" "$LOG" | awk '{print $3}')
    [ -z "$best" ] && best=ERR
    printf '%s\t%s\t%s\t%s\t%s\n' "$N" "$b" "$(head -c 40 $G/$b.name | tr -d '\t')" "$T" "$best" >> "$OUT"
    [ "$best" = "0" ] && echo "HIT $b $T" >> "$OUT"
  done
done
