#!/bin/bash
# scanwl.sh BASE(.wl) GROUPLIST SECS SEED OUTTSV FROM TO : wl2 SA of BASE over each meta group in lines FROM..TO
cd "$(dirname "$0")"
BASE=$1; LIST=$2; SECS=$3; SEED=$4; OUT=$5; FROM=$6; TO=$7
B=$(basename "$BASE" .wl)
sed -n "${FROM},${TO}p" "$LIST" | while read N SPEC; do
  tag=$(echo "$SPEC" | tr ':' '_')
  bin=grp/$tag.bin
  [ -f "$bin" ] || python3 ../tools/groups.py "$(echo $SPEC | sed 's/meta:/meta /; s/:/ /g')" "$bin" > /dev/null 2>&1
  if [ ! -f "$bin" ]; then printf "%s\t%s\tnobin\n" "$N" "$SPEC" | tee -a "$OUT"; continue; fi
  line=$(timeout $((SECS+60)) nice -n 10 ./wl2 "$BASE" "$bin" 9 "$SECS" "$SEED" "out/wl_${B}_$tag" 2>/dev/null | grep '^RESULT' | tail -1)
  cost=$(echo "$line" | sed -n 's/.*cost=\([0-9-]*\).*/\1/p')
  printf "%s\t%s\t%s\n" "$N" "$SPEC" "${cost:-fail}" | tee -a "$OUT"
  rm -f "$bin"
done
