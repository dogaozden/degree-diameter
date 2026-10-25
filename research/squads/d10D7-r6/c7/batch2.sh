#!/bin/bash
# after the tabu run: remaining E7 root-subsystem families, 60 s clique limit each
cd /home/user/degree-diameter/research/squads/d10D7-r6/c7
while pgrep -f "[t]abu_run.sh" >/dev/null || pgrep -f "[p]otabu2 /home" >/dev/null; do sleep 5; done
timeout 1000 nice -n 10 python3 sub11c.py A6 A5 D4A1^3 A3A3A1 A4A2A1 A2^3A1 A3A2A2 D5A1A1 D4A2 A1^7 > batch2.log 2>&1
echo "batch2 done $(date -u +%T)" >> batch2.log
