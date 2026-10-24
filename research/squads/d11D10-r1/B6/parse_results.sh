#!/bin/bash
# prints one line per run: RESULT best/evals/time and the MT stats line (if any), plus the TRACE line for smoke runs
cd /home/user/degree-diameter/research/squads/d11D10-r1/B6
for f in smoke_base smoke_mt0 smoke_mt3 smoke_mt4 cmp_base_s1 cmp_mt3_s1 cmp_base_s2 cmp_mt3_s2 cmp_base_s3 cmp_mt3_s3; do
  [ -f "$f.log" ] || continue
  printf "%-14s %s" "$f" "$(grep -h '^RESULT' "$f.log" | sed -E 's/ x Z_[0-9]+ N=[0-9]+//; s/ orbit .*//' )"
  t=$(grep -h '^TRACE' "$f.log"); [ -n "$t" ] && printf "  %s" "$t"
  m=$(grep -h '^MT=' "$f.log"); [ -n "$m" ] && printf "  [%s]" "$m"
  printf "\n"
done
