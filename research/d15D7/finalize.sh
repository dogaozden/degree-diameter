#!/bin/sh
# finalize.sh SOL K THREADS: check a (15,7) hub solution and file it in research/frontier/sols (cell-15-7 job).
# 1. kcopy_hub check (BFS from freed sources and hubs; decides the diameter by the lemma in kcopy_hub.c), k = 3, 2, 1
# 2. kcopy_hub edges -> edge list; apsp_sym (independent: reads only the edge list, verifies that the copy rotation is
#    an automorphism, BFS from every orbit representative); sha256 of the edge list
# 3. gzip the solution into research/frontier/sols/d15D7_hex11_7copy_K{K}_n{n}.sol.gz with a .check.txt
set -e
SOL=$1; K=$2; T=${3:-3}
cd "$(dirname "$0")"
N=177156; n=$((7 * 2 * N + 6 * K))
OUT=../frontier/sols/d15D7_hex11_7copy_K${K}_n${n}
E=edges_K${K}.txt
{
  echo "(15,7) $n: 7 copies of H(11) + $((6 * K)) hubs ($K freed flags). cell-15-7 job, $(date -u +%Y-%m-%dT%H:%MZ)."
  echo "Solution file (d7hex format: freed points, hub edges, bijection M) = $(basename $OUT).sol.gz; sha256 of the uncompressed file: $(sha256sum $SOL | cut -c1-64)"
  echo "Rebuild: research/d15D7/README.md (hexgen 11, then kcopy_hub check|full|edges hex/hex_q11.bin SOL 3)."
  echo
  echo "1. kcopy_hub check, 7 copies (BFS from all freed sources and hubs):"
  ./kcopy_hub check hex/hex_q11.bin $SOL 3
  echo
  echo "   same bijection, 5 and 3 copies ((14,7) and (13,7) versions):"
  ./kcopy_hub check hex/hex_q11.bin $SOL 2 | tail -2
  ./kcopy_hub check hex/hex_q11.bin $SOL 1 | tail -2
  echo
  ./kcopy_hub edges hex/hex_q11.bin $SOL 3 $E 2>&1
  echo "edge list sha256 (kcopy_hub edges order): $(sha256sum $E | cut -c1-64)"
  echo
  echo "2. apsp_sym (independent edge-list check with the copy rotation verified as an automorphism):"
  ./apsp_sym $E 15 7 $((2 * N)) 7 $T 2>/dev/null
} > $OUT.check.txt 2>&1
gzip -9 -c $SOL > $OUT.sol.gz
rm -f $E
cat $OUT.check.txt
