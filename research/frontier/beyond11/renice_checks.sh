#!/bin/bash
# renice_checks.sh (job beyond-d11b): keep every running haarcheck_gen at nice -5 while the check queue runs, so the
# squad cards (nice 10) take only spare cycles from the ~11 GB checks.
while pgrep -f "qb5.sh" >/dev/null; do
  for p in $(pgrep -x haarcheck_gen); do renice -n -5 -p $p >/dev/null 2>&1; done; sleep 30; done
