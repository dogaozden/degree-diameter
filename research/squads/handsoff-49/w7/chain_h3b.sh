#!/bin/bash
# start the second order-3 queue after the first one has finished
cd /home/user/degree-diameter/research/squads/handsoff-49/w7
while pgrep -f "[r]un_h3.sh" > /dev/null; do sleep 15; done
./run_h3b.sh "PSL2_13*cyc 7" "PSL2_7*cyc 46" "PGL2_7*cyc 23" "PGL2_11*cyc 6" "PSL2_11*cyc 12" "PSL2_13*cyc 8"
