#!/bin/bash
# usage: sweep_chart.sh JOBS OUT   (JOBS lines: base|table|patterns|seconds|seed); perfect controllers are saved
while IFS='|' read -r base tab pat secs seed; do
  tag=$(basename $base .txt)_$(basename $tab .txt)_$(basename $pat .txt)_s$seed
  r=$(timeout $((secs + 30)) nice -n 10 /tmp/claude-0/mlift_chart "$base" "$tab" "$pat" "$secs" "$seed" 2.0 /tmp/claude-0/mc_$tag.edges 2>&1 | tail -1)
  echo "$base|$tab|$pat|$seed|$r" >> "$2"
done < "$1"
