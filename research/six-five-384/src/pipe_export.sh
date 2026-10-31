#!/bin/bash
# pipe_export.sh: exporter half of the pipeline (job six-five-384). Walks data/todo_haar.txt in order, skips ids with a
# DONE log or listed in data/excluded.txt, exports batches of 30 with hx_export_pc.g into $Q, keeping at most ~120
# files queued. Writes $Q/EXPORT_DONE at the end. Run from research/six-five-384. Env: GAP, Q.
set -u
mkdir -p $Q
todo=$(awk 'NR==FNR {ex[$1]=1; next} !($1 in ex)' data/excluded.txt data/todo_haar.txt)
batch=()
flush() {
  [ ${#batch[@]} -eq 0 ] && return
  while [ $(ls $Q | grep -c '^pc_') -gt 120 ]; do sleep 2; done
  $GAP -q -c "IDS:=[$(IFS=,; echo "${batch[*]}")];; DIR:=\"$Q\";;" src/hx_export_pc.g > /dev/null 2>&1
  batch=()
}
for i in $todo; do
  [ -e logs/h384_$i.log ] && grep -q '^DONE' logs/h384_$i.log && continue
  batch+=($i)
  [ ${#batch[@]} -ge 30 ] && flush
done
flush
touch $Q/EXPORT_DONE
