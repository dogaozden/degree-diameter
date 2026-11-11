#!/bin/bash
# check_b.sh STEM d D: build_haar2.py (Haar rebuild, both BFS) and apsp (all pairs on the rebuilt edge list) for a
# research/frontier/sols/<STEM>.txt solution; log in research/frontier/runs/cloudcheck/<STEM>.check.txt (job beyond-d11b)
cd /home/user/degree-diameter/research/frontier; s=$1; d=$2; D=$3; out=runs/cloudcheck/$s.check.txt; e=/tmp/claude-0/chk/$s.edges
{ echo "check of sols/$s.txt (job beyond-d11b, director), $(date -u +%FT%TZ)"; echo "sha256 $(sha256sum sols/$s.txt)"
  echo "== build_haar2.py"; python3 build_haar2.py sols/$s.txt $e
  echo "== apsp (research/lifts/coordinator_check/apsp.c) on that edge list"; t0=$(date +%s)
  /home/user/degree-diameter/research/squads/beyond11b/bin/apsp $e $d $D; echo "apsp time $(( $(date +%s) - t0 )) s"; } > $out 2>&1
grep -h "VALID" $out
