#!/bin/bash
cd /home/user/degree-diameter/research/squads/f65r1/c16
b=$1; m=$2
timeout 200 nice -n 10 ./lift search bases/$b.txt 5 30 7 8 out/$b.m$m.sol cyc $m > logs/$b.m$m.log 2>&1
