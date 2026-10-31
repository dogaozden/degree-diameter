#!/bin/bash
# run_chunk.sh CHUNKFILE: export the groups (ids of order 384, one per line) in one GAP session, run haarex4 on each,
# keep the log without PAIR lines in logs/h384_<id>.log, delete the export. Skips ids whose log has a DONE line and
# ids listed in data/excluded.txt.
# Run from research/six-five-384. Env: GAP (gap binary), HX (haarex4 binary), TMPD (scratch dir).
set -u
chunk=$1; base=$(basename $chunk); d=$TMPD/$base; mkdir -p $d
ids=$(for i in $(cat $chunk); do
  [ -e logs/h384_$i.log ] && grep -q '^DONE' logs/h384_$i.log && continue
  grep -q "^$i " data/excluded.txt && continue     # excluded by an exact filter (README)
  echo $i; done | paste -sd,)
[ -z "$ids" ] && { rmdir $d; exit 0; }
$GAP -q -c "IDS:=[$ids];; DIR:=\"$d\";;" src/hx_export_batch.g > $d/export.log 2>&1
for i in ${ids//,/ }; do
  f=$d/hx_384_$i.txt
  [ -s $f ] || { echo "EXPORTFAIL $i" >> logs/failures.txt; continue; }
  s=$(date +%s.%N)
  $HX $f | grep -v '^PAIR' > logs/h384_$i.tmp
  e=$(date +%s.%N)
  echo "SECS $(echo "$e - $s" | bc)" >> logs/h384_$i.tmp
  mv logs/h384_$i.tmp logs/h384_$i.log
  rm -f $f
done
rm -rf $d
