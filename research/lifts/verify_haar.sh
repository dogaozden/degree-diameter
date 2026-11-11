#!/bin/bash
# Four checks for a haar_gen3 solution file: research/frontier/build_haar2.py (repo checker), haar2lift.py + lift check,
# verify_lift.py (independent Python rebuild), apsp (all-pairs BFS, no symmetry). Writes sols/TAG.txt and verify/TAG.txt.
# Usage: ./verify_haar.sh HAARSOL TAG
cd "$(dirname "$0")"
S=$1; T=$2; E=${TMPDIR:-/tmp/claude-0/-home-user-degree-diameter/ee2ddafa-df45-5cb8-b9ed-a65866641afb/scratchpad}/$T
python3 haar2lift.py $S > sols/$T.txt
{ echo "== research/frontier/build_haar2.py (repo checker, unmodified)"; python3 ../frontier/build_haar2.py $S $E.b2.edges
  echo "== lift check"; ./lift check sols/$T.txt
  echo "== verify_lift.py"; python3 -I verify_lift.py sols/$T.txt $E.edges
  echo "== apsp (all-pairs, no symmetry)"; ./apsp $E.edges 2; } > verify/$T.txt 2>&1
grep -E "^VALID|target D|SUMMARY|RESULT diameter|edge list sha256 =" verify/$T.txt
