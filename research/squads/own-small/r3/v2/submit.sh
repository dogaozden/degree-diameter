#!/bin/bash
# usage: submit.sh "p N id seed GROUPSFILE [STARTFILE]" ... ; each arg is one task (secs 90, D 9)
S=/home/user/degree-diameter/research/squads/own-small
for t in "$@"; do
  set -- $t
  line="r3v2 salift_s $1 $2 $3 9 90 $4 $5${6:+ $6}"
  flock $S/runs/queue/lock -c "echo '$line' >> $S/runs/queue/tasks.txt"
  echo "$line"
done
