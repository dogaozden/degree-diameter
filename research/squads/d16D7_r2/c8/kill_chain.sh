#!/bin/bash
for p in $(ps -eo pid,args | grep -E "chain1.sh|quot2_" | grep -v grep | grep -v kill_chain | awk '{print $1}'); do kill $p 2>/dev/null; done
