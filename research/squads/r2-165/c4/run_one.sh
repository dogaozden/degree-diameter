#!/bin/bash
# args: BASE_NAME GROUP_NAME PATTERN_NAME ; appends one RESULT line per job to sweep_results.txt
B=/home/user/degree-diameter/research/theorems/squad165
base=$1; grp=$2; pat=$3
tag="${base}__${grp}__${pat}"
r=$(timeout 900 nice -n 10 /tmp/claude-0/r2c4/mlift_exh "$B/$base.txt" "/tmp/claude-0/r2c4/$grp.txt" "$B/charts/$pat.txt" "/tmp/claude-0/r2c4/out/$tag.edges" 2>&1 | tail -1)
echo "$tag | $r" >> /tmp/claude-0/r2c4/sweep_results.txt
