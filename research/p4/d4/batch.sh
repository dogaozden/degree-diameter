#!/bin/bash
# usage: batch.sh q mode secs spec...
PY=/private/tmp/claude-501/-Users-dogaozden-AI-Projects-degree-diameter/d6bfe58f-ec9f-4fe8-a39d-9588c6bb9afc/scratchpad/venv/bin/python
q=$1; mode=$2; secs=$3; shift 3
for s in "$@"; do
  tag=$(echo "$s" | tr ':+' '_-')
  echo "== $s" 
  $PY cp_m.py $q $mode $secs --workers 1 --sym "$s" --out sols/${mode}_q${q}_${tag}.json 2>&1 | grep -v "^q="
done
