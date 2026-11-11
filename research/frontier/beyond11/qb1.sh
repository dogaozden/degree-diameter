#!/bin/bash
# qb1.sh (job beyond-d11b): director searches for the 30-billion-vertex cells, one at a time (7.7 GB each), search only.
cd "$(dirname "$0")"; export NOCHECK=1
while pgrep -f "haar_big0 16 11" >/dev/null; do sleep 5; done
./hq.sh 14 12 900 1 4 psl 241 2143 "3 4 2" 4
./hq.sh 13 12 900 1 4 psl 181 5059 "3 4 1" 4
./hq.sh 12 12 1500 1 4 psl 241 2143 "3 4 0" 4
./hq.sh 15 11 2700 1 4 sl 617 61 "3 5 0" 4
echo "QB1 DONE $(date -u +%T)"
