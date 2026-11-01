#!/bin/bash
# scanlift.sh D p LIST SECS OUTDIR [SEEDS]: joint base+voltage annealing (salift_s) of p+p cubic lifts over every group
# "N m k r ..." of LIST (one line per group, in file order), SECS seconds per seed (default seeds: 1). On cost 0 the
# solution is rebuilt by sol2edges.py and checked all-pairs by apsp at D (and D-1); a line goes to OUTDIR/scan.log.
# Example: tools/scanlift.sh 13 4 runs/g_d13_p4.txt 60 runs/s13 "1 2"
H=$(cd "$(dirname "$0")/.." && pwd); D=$1; p=$2; L=$3; S=$4; O=$5; SEEDS=${6:-1}
mkdir -p "$O"
while read N m k r rest; do
  [ -z "$N" ] && continue; case "$N" in \#*) continue;; esac
  tag=g${N}_${m}_${k}_${r}; tab=$O/$tag.tab
  [ -f "$tab" ] || python3 "$H/tools/gtab.py" "$tab" $m $k $r 2>/dev/null
  for s in $SEEDS; do
    out=$O/${tag}_D${D}_p${p}_s$s.sol
    res=$(D=$D timeout $((S + 30)) nice -n 5 "$H/bin/salift_s" $p "$tab" 1 $s $S 10 0.3 "$out" | tail -1)
    best=$(echo "$res" | awk '{print $3}')
    line="N=$N n=$((2 * p * N)) m=$m k=$k r=$r seed=$s best=$best"
    if [ "$best" = "0" ]; then
      python3 "$H/tools/sol2edges.py" "$out" $m $k $r "${out%.sol}.edges" > /dev/null
      chk=$("$H/bin/apsp" "${out%.sol}.edges" 3 $D | tail -1); chk1=$("$H/bin/apsp" "${out%.sol}.edges" 3 $((D - 1)) | tail -1)
      line="$line | $chk | at D-1: $chk1"
    fi
    echo "$line" >> "$O/scan.log"; echo "$line"
    [ "$best" = "0" ] && break
  done
  rm -f "$tab"
done < "$L"
