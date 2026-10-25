#!/bin/bash
# verify.sh SOLFILE : independent checks. build_haar2.py (<= 20M vertices), apsp.c all-pairs on the edge list.
# usage: verify.sh path/to/d6D8_xxx.txt
F=$1
cd /home/user/degree-diameter/research/frontier
python3 build_haar2.py "$F" 2>&1 | tail -n 4
