#!/bin/bash
# kill the queued/running DLX wrapper of card c8 (old binary)
for p in $(ps -eo pid,args | grep -F "c8/dlx " | grep -v grep | grep -v kill_q | awk '{print $1}'); do kill $p 2>/dev/null; done
