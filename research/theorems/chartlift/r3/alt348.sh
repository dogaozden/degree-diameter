#!/bin/bash
# (4,3) alternation: (a) anneal voltages with labelled singular set S (r3/flags43/sNNN.flags), (b) score the best
# voltages against all 348 sets and switch to the best one; stop at cost 0.
# usage: r3/alt348.sh BASE GROUP START_SET ROUNDS SECONDS OUTDIR
base=$1; grp=$2; S=$3; rounds=$4; t=$5; out=$6
W=/tmp/claude-0/-home-user-degree-diameter/8e7a80fa-6b09-58cb-8199-8d05845bbe55/scratchpad/w; mkdir -p $out
for r in $(seq 1 $rounds); do
  WRITEBEST=1 nice -n 5 $W/ctrl_search $base $grp r3/flags43/s$S.flags $t $r $out/v$r > $out/ctrl$r.out 2>&1
  c=$(tail -n 1 $out/ctrl$r.out | sed 's/.*best_cost=\([0-9]*\).*/\1/')
  v=$(tail -n +2 $out/v$r.volt | awk '{print $4}' | paste -sd,)
  read c2 f2 <<< "$(r3/score348.sh $base $grp $v)"
  S2=$(echo $f2 | sed 's/.*s\([0-9]*\)\.flags/\1/')
  echo "round $r: set s$S cost $c; best over 348 sets at these voltages: s$S2 cost $c2"
  if [ "$c2" = "0" ]; then cp $out/v$r.volt $out/final.volt; echo "s$S2" > $out/final.set; echo "DONE cost 0 with set s$S2"; exit 0; fi
  S=$S2
done
echo "no cost 0 after $rounds rounds"
