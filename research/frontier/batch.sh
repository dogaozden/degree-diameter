#!/usr/bin/env bash
# usage: batch.sh JOBFILE ; each line: d D seconds seed K group...   (stops a d,D after its first solution unless KEEP=1)
cd "$(dirname "$0")"
while read -r d D secs seed K grp; do
  [ -z "$d" ] && continue; case "$d" in \#*) continue;; esac
  tag=$(echo "d${d}D${D}_${grp}_s${seed}" | tr ' ' '_')
  [ -f "sols/$tag.txt" ] && continue
  echo "$(date +%T) start $tag"
  ${BIN:-./haar_gen} $d $D $secs $seed $K "sols/$tag.txt" $grp > "runs/$tag.log" 2>&1
  echo "$(date +%T) end $tag: $(grep RESULT runs/$tag.log)"
done < "$1"
