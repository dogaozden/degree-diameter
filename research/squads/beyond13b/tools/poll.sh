#!/bin/bash
# poll.sh TAG [TAG ...]: wait up to 95 s (less if every run has ended), then for each run print RUNNING or FINISHED,
# minutes since it started, its last two log lines and any RESULT line. Each call returns within 100 s.
end=$(( $(date +%s) + 95 ))
while [ $(date +%s) -lt $end ]; do
  alive=0; for t in "$@"; do kill -0 $(cat out/$t.pid) 2>/dev/null && alive=1; done
  [ $alive = 0 ] && break; sleep 3
done
for t in "$@"; do
  st=FINISHED; kill -0 $(cat out/$t.pid) 2>/dev/null && st=RUNNING
  echo "== $t $st after $(( ($(date +%s) - $(cat out/$t.t0)) / 60 )) min"
  grep -v '^RESULT' out/$t.log | tail -n 2 | cut -c1-220
  grep '^RESULT' out/$t.log | tail -n 1 | cut -c1-300
done
echo "now $(date -u +%T)"
