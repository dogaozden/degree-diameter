#!/bin/bash
# Run job files from a spool directory with at most P at a time (P = number of CPU slots to use).
# usage: pool.sh DIR P
#   DIR/<name>.jobs  an orbq.sh job file: run as  orbq.sh DIR/<name>.jobs DIR/<name>/   (one slot)
#   DIR/<name>.cmd   any shell command line (one slot), output in DIR/<name>.out
# Files are started in name order (prefix them 10-, 20-, ... to order them); new files can be added at any time.
# A file is started only while fewer than P search processes (haar_sym, haar_fast, anyone's) run on the machine.
# A started file gets DIR/<name>.started; DIR/P (if present) overrides P on the fly; touch DIR/STOP to stop the
# pool after the running files finish.
# After a machine restart just start pool.sh again: it clears the .started markers of *.jobs files (orbq.sh skips
# finished jobs and resumes unfinished ones from their checkpoints).
DIR=$1; P0=${2:-4}; HERE=$(cd "$(dirname "$0")" && pwd)
rm -f "$DIR"/*.jobs.started
declare -A pid
while [ ! -e "$DIR/STOP" ] || [ ${#pid[@]} -gt 0 ]; do
  for n in "${!pid[@]}"; do kill -0 "${pid[$n]}" 2>/dev/null || { echo "$(date +%T) end   $n"; unset "pid[$n]"; }; done
  P=$P0; [ -s "$DIR/P" ] && P=$(cat "$DIR/P")
  if [ ! -e "$DIR/STOP" ]; then
    for f in $(ls "$DIR"/*.jobs "$DIR"/*.cmd 2>/dev/null | sort); do
      [ "$(pgrep -c -x 'haar_sym|haar_fast')" -ge "$P" ] && break
      n=$(basename "$f"); [ -e "$DIR/$n.started" ] && continue
      touch "$DIR/$n.started"; echo "$(date +%T) start $n"
      case "$f" in
        *.jobs) mkdir -p "$DIR/${n%.jobs}"; "$HERE/orbq.sh" "$f" "$DIR/${n%.jobs}" > "$DIR/${n%.jobs}/queue.log" 2>&1 & ;;
        *.cmd)  bash "$f" > "$DIR/${n%.cmd}.out" 2>&1 & ;;
      esac
      pid[$n]=$!; sleep 5
    done
  fi
  sleep 15
done
