#!/bin/bash
cd "$(dirname "$0")"; export NOCHECK=1
./hq.sh 11 12 1200 1 4 sl 307 181 "3 3 2" 2
./hq.sh 12 12 1200 1 4 psl 503 157 "3 4 0" 2
./hq.sh 13 12 1200 1 4 psl 307 691 "3 4 1" 2
echo Q2 DONE
