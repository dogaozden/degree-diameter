#!/bin/bash
cd /home/user/degree-diameter/research/cell147/units/uni11
while kill -0 12100 2>/dev/null; do sleep 3; done
./tw.sh < tw13.txt > tw13.log 2>&1
./tw.sh < tw11.txt > tw11.log 2>&1
echo done > tw_queue.done
