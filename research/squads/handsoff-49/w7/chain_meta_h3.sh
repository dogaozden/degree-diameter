#!/bin/bash
cd /home/user/degree-diameter/research/squads/handsoff-49/w7
while pgrep -f "[r]un_perfect2.sh" > /dev/null; do sleep 10; done
./meta_h3_screen.sh
