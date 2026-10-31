#!/bin/bash
# Run a queue of haar_sd jobs, P at a time.  QUEUE lines: TAG|ENV assignments|d D secs seed K|GROUP... n
# Each job: env THREADS=1 ENV haar_sd d D secs seed K OUTDIR/TAG.sol GROUP... n > OUTDIR/TAG.log; jobs whose log exists are skipped.
# usage: hsd_queue.sh QUEUE OUTDIR P
here=$(cd "$(dirname "$0")" && pwd)
q=$1; out=$2; P=$3; mkdir -p "$out"
grep -v '^#' "$q" | grep -v '^$' | xargs -d '\n' -P "$P" -I{} bash -c '
  IFS="|" read -r tag envs pre grp <<< "{}"
  [ -e "'"$out"'/$tag.log" ] && exit 0
  env THREADS=1 $envs nice -n 5 "'"$here"'/haar_sd" $pre "'"$out"'/$tag.sol" $grp > "'"$out"'/$tag.log" 2>&1
'
