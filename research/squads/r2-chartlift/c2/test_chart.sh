#!/bin/bash
# squad c2: test one chart as controller flags on one group.  usage: test_chart.sh CHART TAG GROUPFILE SECONDS
# writes c2/TAG.flags, c2/TAG.volt/.ctrl (cost 0 only), c2/TAG.search.log; if cost 0 builds the lift and checks it with apsp
C=/home/user/degree-diameter/research/squads/r2-chartlift/c2
CH=$1; TAG=$2; G=$3; S=$4
cd /home/user/degree-diameter/research/theorems/chartlift || exit 1
python3 chartflags.py $CH 3 5 $C/$TAG.flags || exit 1
timeout 900 nice -n 10 $C/ctrl_search bases5/k5r1_000.txt $G $C/$TAG.flags $S 1 $C/$TAG > $C/$TAG.search.log 2>&1
echo "$TAG $(basename $G) $(tail -n 1 $C/$TAG.search.log | cut -c1-120)"
if [ -f $C/$TAG.ctrl ]; then
  python3 lift.py $C/$TAG.ctrl $CH 3 5 $C/$TAG.edges && timeout 900 nice -n 10 $C/apsp $C/$TAG.edges 15 5 | tail -n 2
  timeout 900 nice -n 10 $C/apsp $C/$TAG.edges 15 4 | tail -n 1
  rm -f $C/$TAG.edges
fi
