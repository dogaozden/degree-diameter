#!/bin/sh
cd /home/user/degree-diameter/research/squads/deep-65b
while pgrep -f "sg_176_23.tab ex" > /dev/null; do sleep 10; done
tools/runq.sh runs/queue2.txt 1
