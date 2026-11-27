#!/bin/bash
cd "$(dirname "$0")"; export CTH=2
./hq.sh 12 11 1500 1 4 sl 263 79 "3 4 0" 2
./hq.sh 13 11 2400 1 4 sl 229 271 "3 4 1" 2
./hq.sh 14 11 3000 1 4 sl 607 31 "3 4 2" 2
echo Q1 DONE
