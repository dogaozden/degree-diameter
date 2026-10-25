#!/bin/bash
cd /home/user/degree-diameter/research/cell147/units
while pgrep -x ucheck12 > /dev/null; do sleep 10; done
./ucheck12 ../data/gh_11.txt cells/d13D7.state cells/d13D7.units 7 2 > cells/d13D7.ucheck.txt 2> cells/d13D7.ucheck.log
./ucheck12 ../data/gh_11.txt cells/d15D7.state cells/d15D7.units 7 2 > cells/d15D7.ucheck.txt 2> cells/d15D7.ucheck.log
./ucheck12 ../data/gh_13.txt cells/d16D7.state cells/d16D7.units 7 2 > cells/d16D7.ucheck.txt 2> cells/d16D7.ucheck.log
