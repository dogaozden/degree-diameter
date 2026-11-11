#!/usr/bin/env bash
# usage: run_jobs.sh JOBFILE SUMMARY ; line: secs seed K group-tokens... n   (4 jobs in parallel, d=7 D=7)
cd "$(dirname "$0")"
run1() {
  line="$1"; set -- $line; secs=$1; seed=$2; K=$3; shift 3
  tag="d7D7_${TAGP:-}$(echo "$*" | tr ' ' '_')_s${seed}"
  ${BIN:-./haar_gen3} 7 7 $secs $seed $K "sols/$tag.txt" "$@" > "runs/$tag.log" 2>&1
  echo "$tag $(grep -h RESULT runs/$tag.log | head -1)" >> "$SUMMARY"
}
export -f run1; export SUMMARY="$2"
grep -v '^#' "$1" | grep . | xargs -P 4 -I{} bash -c 'run1 "{}"'
