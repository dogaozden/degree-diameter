#!/bin/bash
# copy raw results and the run scripts (small text files only) into the card folder
D=/home/user/degree-diameter/research/squads/r2-165/c3
mkdir -p $D/scripts
{ echo "# screen: TAG BASE TABLE PATTERN BEST_COST  (cyc13, cyc14, dih7: 3 s CPU per run; other groups: 2 s CPU per run, 8 bases each)"; cat /tmp/claude-0/r2c3/res_screen.txt; } > $D/results_screen.txt
if [ -s /tmp/claude-0/r2c3/res_phaseC.txt ]; then { echo "# phase C: TAG BASE TABLE PATTERN BEST_COST  (20 s CPU, two seeds on each target's best screen candidate)"; cat /tmp/claude-0/r2c3/res_phaseC.txt; } > $D/results_phaseC.txt; fi
cp /tmp/claude-0/r2c3/run1.sh /tmp/claude-0/r2c3/make_phaseC.sh /tmp/claude-0/r2c3/phaseC.sh /tmp/claude-0/r2c3/verify.sh /tmp/claude-0/r2c3/collect.sh $D/scripts/
cp /tmp/claude-0/r2c3/jobs_phaseC.txt $D/scripts/ 2>/dev/null || true
ls $D $D/scripts
