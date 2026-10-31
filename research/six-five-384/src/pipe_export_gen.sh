#!/bin/bash
# pipe_export_gen.sh ORD...: exporter for other orders (job six-five-384, orders 401-450). For each order, all ids in
# batches of 20 through hx_export_gen.g into $Q (at most ~80 files queued); ABELIAN/RANK lines are appended to
# $OUT/filtered.txt. Ids with a DONE log in $OUT/logs are skipped. Writes $Q/EXPORT_DONE at the end. Env: GAP, Q, OUT.
set -u
mkdir -p $Q $OUT/logs
for o in "$@"; do
  n=$($GAP -q -c "Print(NrSmallGroups($o), \"\\n\"); QUIT;" 2>/dev/null | tr -d '\r')
  batch=()
  for i in $(seq 1 $n); do
    [ -e $OUT/logs/h${o}_$i.log ] && grep -q '^DONE' $OUT/logs/h${o}_$i.log && continue
    grep -q "^[A-Z]* $o $i\( \|$\)" $OUT/filtered.txt 2>/dev/null && continue
    batch+=($i)
    if [ ${#batch[@]} -ge 20 ] || [ $i -eq $n ]; then
      while [ $(ls $Q | grep -c -E '^(pc|hx)_') -gt 80 ]; do sleep 2; done
      $GAP -q -c "ORD:=$o;; IDS:=[$(IFS=,; echo "${batch[*]}")];; DIR:=\"$Q\";;" src/hx_export_gen.g 2>/dev/null | grep -E '^(ABELIAN|RANK) ' >> $OUT/filtered.txt
      batch=()
    fi
  done
  if [ ${#batch[@]} -gt 0 ]; then
    $GAP -q -c "ORD:=$o;; IDS:=[$(IFS=,; echo "${batch[*]}")];; DIR:=\"$Q\";;" src/hx_export_gen.g 2>/dev/null | grep -E '^(ABELIAN|RANK) ' >> $OUT/filtered.txt
  fi
done
touch $Q/EXPORT_DONE
