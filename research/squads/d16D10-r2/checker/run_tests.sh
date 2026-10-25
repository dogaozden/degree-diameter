#!/bin/bash
# Runs hcheckpsl and the reference hcpsl on the test files, one process at a time.
# usage: run_tests.sh LISTFILE OUTTSV   (LISTFILE: one file path per line)
CHK=/home/user/degree-diameter/research/squads/d16D10-r2/checker
REF=/tmp/claude-0/-home-user-degree-diameter/44b9d801-e3b0-5931-8a0d-00a602da11d2/scratchpad/bin/hcpsl
LIST=$1; OUT=$2
printf "file\tours_verdict\tours_exit\tours_wall_s\tours_ecc\tref_verdict\tref_exit\tref_wall_s\tagree\n" > "$OUT"
while read -r f; do
  [ -z "$f" ] && continue
  b=$(basename "$f" .txt)
  # ours
  t0=$(date +%s.%N)
  o=$( (ulimit -v 2097152; THREADS=2 nice -n 10 timeout 600 "$CHK/hcheckpsl" "$f" > "$CHK/logs/$b.ours.out" 2> "$CHK/logs/$b.ours.err"); echo $? )
  t1=$(date +%s.%N)
  # reference
  r=$( (ulimit -v 2097152; THREADS=2 nice -n 10 timeout 600 "$REF" "$f" > "$CHK/logs/$b.ref.out" 2> "$CHK/logs/$b.ref.err"); echo $? )
  t2=$(date +%s.%N)
  ov=$(head -1 "$CHK/logs/$b.ours.out" | awk '{print $1}'); [ -z "$ov" ] && ov="NONE"
  ecc=$(sed -n 2p "$CHK/logs/$b.ours.out" | tr -d '\n')
  rv=$(grep -m1 -oE '^(VALID|INVALID)' "$CHK/logs/$b.ref.out"); [ -z "$rv" ] && rv="NONE"
  ag=yes; [ "$ov" != "$rv" ] && ag=NO
  printf "%s\t%s\t%s\t%.2f\t%s\t%s\t%s\t%.2f\t%s\n" "$b" "$ov" "$o" "$(echo "$t1 - $t0" | bc)" "$ecc" "$rv" "$r" "$(echo "$t2 - $t1" | bc)" "$ag" >> "$OUT"
done < "$LIST"
echo "done -> $OUT"
