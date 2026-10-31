#!/bin/bash
# exh_queue.sh LIST: exhaustive sdk (K = $K, default 9) on every group of LIST, one per line:
#   sg N ID  |  meta2 M KK R  |  gapf TAG PRELUDE.g "GAP assignments"
# GAP export with the centralizer generators (first-orbit normalisation), cached in $TMPDIR/deep as deep_tabu.sh /
# deep_gapf.sh do; sdk with TYPES (default 1,3,5), MAXEV = MAXEVF = CAP (default 4e9), SAMPLE=0 (enumerate fully,
# CAPPED if cut), NEAR=25.  Output logs/K$K/exh/<tag>.out, one summary line per group in logs/K$K/exh/summary.txt.
R0="$(cd "$(dirname "$0")/.." && pwd)"; K=${K:-9}; T=${TMPDIR:-/tmp}/deep; mkdir -p $T $R0/logs/K$K/exh $R0/cand
NOEXT="NOEXT:=1;;"; [ $((K % 2)) -eq 0 ] && NOEXT=""
while read -r kind a b c d; do
  [ -z "$kind" ] && continue
  if [ $kind = sg ]; then tag=${a}_${b}; F=$T/g$tag.ht
    [ -s $F ] || nice gap -q -c "N:=$a;; ID:=$b;; OUT:=\"$F\";; $NOEXT" $R0/src/export_sd.g > /dev/null 2>&1
  elif [ $kind = meta2 ]; then tag=c${a}_${b}_${c}; F=$T/$tag.ht
    if [ ! -s $F ]; then cat $R0/src/meta_group2.g $R0/src/export_sd.g > $T/run_$tag.g
      nice gap -q -c "M0:=$a;; K0:=$b;; R0:=$c;; OUT:=\"$F\";; $NOEXT" $T/run_$tag.g > /dev/null 2>&1; rm -f $T/run_$tag.g; fi
  else tag=$a; F=$T/g$tag.ht
    if [ ! -s $F ]; then cat $R0/$b $R0/src/export_sd.g > $T/run_$tag.g
      nice gap -q -c "$c OUT:=\"$F\";; $NOEXT" $T/run_$tag.g > /dev/null 2>&1; rm -f $T/run_$tag.g; fi
  fi
  O=$R0/logs/K$K/exh/$tag.out; t0=$(date +%s)
  K=$K TYPES=${TYPES:-1,3,5} MAXEV=${CAP:-4000000000} MAXEVF=${CAP:-4000000000} SAMPLE=0 NEAR=25 EDGES=$R0/cand/exh${K}_$tag.edges nice -n 5 $R0/src/sdk $F > $O 2>&1
  best=$(grep "^TYPE" $O | awk '{for(i=1;i<NF;i++) if ($i=="best") print $(i+1)}' | sort -n | head -1)
  echo "$kind $a $b $c tag $tag types $(grep -c '^TYPE' $O) capped $(grep -c CAPPED $O) best $best sols $(grep -c '^SOL' $O) secs $(( $(date +%s) - t0 ))" >> $R0/logs/K$K/exh/summary.txt
  grep -q "^SOL" $O && echo "HIT exh $tag K $K" >> $R0/logs/K$K/HITS.txt
done < "$1"
echo "QUEUE DONE $1 $(date -u +%H:%M)" >> $R0/logs/K$K/exh/summary.txt
