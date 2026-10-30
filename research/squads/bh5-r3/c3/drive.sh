#!/bin/bash
# c3 driver: same as coset/run_group.sh but with a per-file time cap (default 60 s) so one group cannot stall the batch.
# usage: drive.sh NAME "GAP expr" H DELTA [FILE_TIMEOUT=60] [MAXSETS=2000000]
name=$1; expr=$2; h=$3; delta=$4; ft=${5:-60}; ms=${6:-2000000}
C=/home/user/degree-diameter/research/beyond-haar-d5/coset
W=/home/user/degree-diameter/research/squads/bh5-r3/c3
cd $C || exit 1
mkdir -p out logs
if [ -z "$SKIP_EXPORT" ]; then timeout 900 nice -n 10 gap -q -c "GNAME:=\"$name\"; G:=$expr; H_ORDER:=$h; OUT:=\"out/${name}_h$h\";" dc_export.g > $W/$name.export 2>&1; fi
echo "export done: $(grep -c pair $W/$name.export) pairs, $(ls out/${name}_h${h}_*.dc 2>/dev/null | wc -l) files" >&2
for f in out/${name}_h${h}_*.dc; do
  [ -e "$f" ] || continue
  r=$(timeout $ft nice -n 10 ./dcenum $f $delta 5 ${f%.dc}.best.edges $ms 2>/dev/null | tail -1)
  [ -z "$r" ] && r="TIMEOUT $f"
  echo "$r"
  rm -f "$f"
done | tee $W/$name.h${h}.d${delta}.result
echo "DRIVE_DONE $name"
