#!/bin/bash
cd /home/user/degree-diameter/research/squads/handsoff-37/r2a
while pgrep -f "run_seeds.sh 30 2 " >/dev/null; do sleep 5; done
./run_seeds.sh 30 2 "19:3:C28 20:3:D14 21:3:Dic7 22:3:C2xD7 23:3:C2xC14 9:6:D7 10:6:C14 12:7:D6 13:7:A4 14:7:Dic3 15:7:C2xC6 16:7:C12 6:12:C7 4:14:S3 5:14:C6 2:21:C4 3:21:C2xC2 1:28:C3"
echo BATCH2_DONE
