#!/bin/bash
# waits until a run reports best=0 (solved) or no haar_sym run is left; prints a status line every 15 min
cd "$(dirname "$0")"
start=$(date +%s)
while true; do
  if grep -l "best=0 " *.log >/dev/null 2>&1; then echo "SOLVED: $(grep -l 'best=0 ' *.log | tr '\n' ' ')"; exit 0; fi
  n=$(pgrep -fc "^\./haar_sym 10 10 10800" || true)
  if [ "$n" = "0" ]; then echo "ALL RUNS ENDED"; exit 0; fi
  if [ $(( $(date +%s) - start )) -gt 11000 ]; then echo "MONITOR TIMEOUT"; exit 0; fi
  for f in *.log; do echo "$(date -u +%H:%M) $f: $(tail -n 1 "$f" | cut -c1-120)"; done
  sleep 900
done
