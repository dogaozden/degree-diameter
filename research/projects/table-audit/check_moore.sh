#!/bin/bash
# Rebuild and check the Moore-bound cells of the table (D = 3, 4, 6; Delta - 1 a prime power), one line per cell.
# D = 3: PG(2,q) incidence graph (moore.py); D = 4: W(q) incidence graph (moore.py);
# D = 6: H(q) incidence graph (research/evenq/hexq.py, the lab's generator; the apsp check is what makes it count).
# Each graph is checked by apsp.c (all-pairs BFS); graphs above 50000 vertices use apsp_mt.c with 4 threads.
# Usage: bash check_moore.sh WORKDIR     (WORKDIR is a scratch directory; graphs are written there, not in the repo)
set -u
W=${1:?usage: check_moore.sh WORKDIR}
HERE=$(cd "$(dirname "$0")" && pwd)
REPO=$(cd "$HERE/../../.." && pwd)
mkdir -p "$W"
gcc -O2 -o "$W/apsp" "$REPO/research/lifts/coordinator_check/apsp.c" 2>/dev/null
gcc -O3 -pthread -o "$W/apsp_mt" "$REPO/research/lifts/coordinator_check/apsp_mt.c" 2>/dev/null
for D in 3 4 6; do
  for q in 2 3 4 5 7 8 9 11 13; do
    d=$((q + 1))
    f="$W/moore_D${D}_q${q}.edges"
    case $D in
      3|4) python3 "$HERE/moore.py" $D $q "$f" >/dev/null ;;
      6) (cd "$REPO/research/evenq" && python3 hexq.py $q "$f" >/dev/null) ;;
    esac
    n=$(head -1 "$f")
    if [ "$n" -gt 50000 ]; then
      res=$("$W/apsp_mt" "$f" $d $D 4 | tail -1)
    else
      res=$("$W/apsp" "$f" $d $D | tail -1)
    fi
    echo "D=$D q=$q Delta=$d n=$n: $res"
  done
done
