#!/bin/bash
# A6 batch: RANDORB=30 for the four 5th roots of unity mod 421 (default ALPHA), one ALPHA cross-check,
# then the best pairing (lowest median) annealed for 600 s with ORBW=5, then haarcheck_psl if solved.
H=/home/user/degree-diameter/research/structured/haar_sym
W=/home/user/degree-diameter/research/squads/d11D10-r1/A6
CHK=/home/user/degree-diameter/research/structured/tools/haarcheck_psl
cd "$W" || exit 1
T0=$(date +%s)
log() { echo "$(date -u +%T) $1 (batch $(( $(date +%s) - T0 )) s)" >> batch1.time; }
run() {   # run TAG [VAR=val ...]: RANDORB=30 screen with ORBIT="5 2 1"
  local tag=$1; shift
  env ORBIT="5 2 1" RANDORB=30 "$@" "$H" 11 10 1 1 8 /dev/null psl 71 421 > randorb30_$tag.log 2>&1
  log "$tag done"
}
for AR in 252 354 377 279; do run AR$AR AR=$AR; done
I=$(sed -n 's/.*conj by \(mat([^)]*)\) (index \([0-9]*\)).*/\2/p' randorb30_AR252.log | head -1)
log "default ALPHA index $I: $(grep 'alpha:' randorb30_AR252.log)"
read I2 < <(python3 psl_index.py 71 "$I" | awk '/M\^2/ {print $NF; exit}')
log "index of g^2 = $I2 (cross-check with AR=252 gives the group of AR=377)"
run ALPHA${I2}_AR252 ALPHA=$I2 AR=252
BEST=$(for AR in 252 354 377 279; do m=$(sed -n 's/.*median=\([0-9]*\).*/\1/p' randorb30_AR$AR.log); echo "$m $AR"; done | sort -n -k1,1 -k2,2 | head -1 | awk '{print $2}')
log "best pairing by median: AR=$BEST"
OUT=$W/d11D10_psl_71_421_orb5_A6ar${BEST}_s1.txt
env ORBIT="5 2 1" ORBW=5 AR=$BEST "$H" 11 10 600 1 8 "$OUT" psl 71 421 > anneal_AR$BEST.log 2>&1
log "anneal AR=$BEST done: $(grep RESULT anneal_AR$BEST.log | tail -1)"
if [ -s "$OUT" ] && grep -q 'best=0' anneal_AR$BEST.log; then
  "$CHK" "$OUT" > haarcheck_AR$BEST.log 2>&1
  log "haarcheck done: $(tail -1 haarcheck_AR$BEST.log)"
fi
log "batch1 finished"
