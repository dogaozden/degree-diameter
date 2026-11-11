#!/bin/sh
# usage: sh run_chunks.sh TABLE NAME   (k = 3; NPROC = 256 splits per R-orbit; resumes from NAME.cur = "QS PS"; TLIM seconds, default 85)
cd "$(dirname "$0")" || exit 1
tab=$1; name=$2
if [ -f "$name.cur" ]; then read QS PS < "$name.cur"; else QS=0; PS=0; fi
if [ "$QS" = "done" ]; then echo "$name: finished"; exit 0; fi
export QS PS TLIM=${TLIM:-85}
./hubk "$tab" 3 ex 256 > "$name.run" 2>&1
cat "$name.run" >> "$name.log"
st=$(grep '^STOP' "$name.run" | tail -1)
if [ -n "$st" ]; then set -- $st; echo "$3 $5" > "$name.cur"; else echo done > "$name.cur"; fi
echo "$name: chunks this call $(grep -c '^CHUNK' "$name.run"), cursor now $(cat "$name.cur")"
awk '/^CHUNK/{L+=$9; P36+=$11; P25+=$13; S+=$15; if(B==""||$17<B) B=$17; R[$5]=1} END{n=0; for(r in R) n++; printf "this call: R-orbits touched %d, leaves %d, pass36 %d, pass25 %d, solutions %d, best_miss %s\n", n, L, P36, P25, S, B}' "$name.run"
