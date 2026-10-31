#!/bin/bash
# summ.sh OUT...: records line and per-type best of fsd outputs
for f in "$@"; do echo "== $f"; grep -E "^(FAMILY|RECORDS)" $f | tr '\n' ' '; echo; grep "^TABU" $f | awk '{for(i=1;i<NF;i++){if($i=="best") b=$(i+1); if($i=="steps") s=$(i+1); if($i=="secs") t=$(i+1)}; printf "%s %s f%s:%s(%ss) ", $3,$4,$6,b,t}'; echo; echo "sols $(grep -c '^SOL' $f)"; done
