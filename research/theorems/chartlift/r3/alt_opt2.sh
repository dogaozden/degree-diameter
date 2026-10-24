#!/bin/bash
# Alternating optimisation (round 3): (a) anneal voltages with the chart fixed (ctrl_search, WRITEBEST),
# (b) re-optimise the chart for that controller (r3/cdesc/star_cd_ctrl.py: objective = uncovered controller targets,
# diagonals and pencils kept), repeat.  Stops at cost 0 and leaves OUT/final.volt, OUT/final.chart.txt.
# Copy of r3/alt_opt.sh with MAXC (env): stop after round 1 if the voltage cost is above MAXC.
# usage: r3/alt_opt2.sh q k BASE GROUPFILE CHART ROUNDS T_ctrl T_chart OUTDIR
q=$1; k=$2; base=$3; grp=$4; chart=$5; rounds=$6; t1=$7; t2=$8; out=$9
W=/tmp/claude-0/-home-user-degree-diameter/8e7a80fa-6b09-58cb-8199-8d05845bbe55/scratchpad/w
mkdir -p $out; cp $chart $out/chart0.txt; cur=$out/chart0.txt
for r in $(seq 1 $rounds); do
  python3 chartflags.py $cur $q $k $out/cur.flags > /dev/null
  WRITEBEST=1 nice -n 5 $W/ctrl_search $base $grp $out/cur.flags $t1 $r $out/v$r > $out/ctrl$r.out 2>&1
  c=$(tail -n 1 $out/ctrl$r.out | sed 's/.*best_cost=\([0-9]*\).*/\1/'); echo "round $r: voltages cost $c"
  if [ -n "$MAXC" ] && [ "$r" = "1" ] && [ "$c" -gt "$MAXC" ]; then echo "STOP round 1 cost $c > MAXC=$MAXC"; exit 0; fi
  if [ "$c" = "0" ]; then cp $out/v$r.volt $out/final.volt; cp $cur $out/final.chart.txt; echo "DONE cost 0 (voltages)"; exit 0; fi
  CTRL=$out/v$r.volt GROUP=$grp nice -n 5 python3 r3/cdesc/star_cd_ctrl.py $q $k $cur $t2 $r $out/chart$r.txt > $out/cd$r.log 2>&1
  if [ -f $out/chart$r.txt.cu0 ]; then
    python3 chartflags.py $out/chart$r.txt.cu0 $q $k $out/cu0.flags > /dev/null
    v=$(tail -n +2 $out/v$r.volt | awk '{print $4}' | paste -sd,)
    c2=$(VOLT=$v $W/ctrl_search $base $grp $out/cu0.flags 1 1 | sed 's/.*cost=\([0-9]*\).*/\1/')
    echo "round $r: chart descent reached controller cost 0; ctrl_search check cost $c2"
    if [ "$c2" = "0" ]; then cp $out/v$r.volt $out/final.volt; cp $out/chart$r.txt.cu0 $out/final.chart.txt; echo "DONE cost 0 (chart)"; exit 0; fi
  fi
  cur=$out/chart$r.txt; echo "round $r: chart descent $(grep -E 'FINAL' $out/cd$r.log)"
done
echo "no cost 0 after $rounds rounds"
