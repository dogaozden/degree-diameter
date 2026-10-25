#!/bin/sh
# usage: mk_del.sh HUB LEVEL OUT  -- drop the hub's main edge at LEVEL (a vertex < 664300 on that level)
awk -v h="$1" -v lev="$2" 'NR==1{print; next} { if (!done && (($1==h && $2<664300 && int($2/132860)==lev) || ($2==h && $1<664300 && int($1/132860)==lev))) {done=1; next} print } END{ if(!done) { print "NOT FOUND" > "/dev/stderr"; exit 1 } }' g.edges > "$3"
