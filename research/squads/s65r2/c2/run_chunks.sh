#!/bin/bash
# runs sweep.sh over 704-order id chunks, top down; stops starting chunks after the DEADLINE (epoch seconds)
cd /home/user/degree-diameter/research/squads/s65r2/c2
for ch in "1338 1387" "1288 1337" "1238 1287" "1188 1237" "1138 1187" "1088 1137" "1038 1087" "988 1037" "938 987" "888 937" "838 887" "788 837" "738 787" "694 737"; do
  set -- $ch
  if [ "$(date +%s)" -ge "$DEADLINE" ]; then echo "STOP before $1-$2 at $(date -u +%T)"; break; fi
  echo "CHUNK $1-$2 start $(date -u +%T)"
  ./sweep.sh 704 2 6 3 "[$1..$2]"
  echo "CHUNK $1-$2 done $(date -u +%T)" 
  echo "$1 $2 $(date -u +%T)" >> logs/progress.txt
done
echo "ALL DONE $(date -u +%T)"
