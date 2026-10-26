#!/bin/bash
# usage: sweep.sh JOBS OUT   (JOBS lines: base_file|table_file|seconds|seed)
while IFS='|' read -r base tab secs seed; do
  r=$(timeout $((secs + 30)) nice -n 10 ./mlift "$base" "$tab" "$secs" "$seed" 2.0 2>&1 | tail -1)
  echo "$base|$tab|$seed|$r" >> "$2"
done < "$1"
