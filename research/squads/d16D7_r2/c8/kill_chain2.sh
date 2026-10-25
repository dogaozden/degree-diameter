#!/bin/bash
for p in $(ps -eo pid,args | grep -E "chain2.sh|wgs_sp.txt|wgs_pt.txt" | grep -v grep | grep -v kill_chain2 | awk '{print $1}'); do kill $p 2>/dev/null; done
