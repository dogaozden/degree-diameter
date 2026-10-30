#!/bin/bash
# Rebuild and check the four 384-vertex (5,5) graphs. Run from research/beyond-haar-d5b.
# Path 1 (GAP): tables of SmallGroup(96, i) -> lift edge lists from the solution lines -> apsp at D = 5 and D = 4.
# Path 2 (no GAP, no tables): voltages as permutations (records/*.perm) -> build_lift_perm.py -> BFS check.
# Both outputs are compared with the saved edge lists up to isomorphism (nauty-labelg).
set -e
T=$(mktemp -d); gcc -O3 -o $T/apsp ../lifts/coordinator_check/apsp.c 2>/dev/null
g6() { python3 -c "
import sys
L=open(sys.argv[1]).read().split('\n'); n=int(L[0]); adj=[[0]*n for _ in range(n)]
for l in L[1:]:
    if l.strip(): a,b=map(int,l.split()); adj[a][b]=adj[b][a]=1
bits=[adj[i][j] for j in range(1,n) for i in range(j)]; bits+=[0]*(-len(bits)%6)
s='~'+''.join(chr(63+((n>>k)&63)) for k in (12,6,0))
print(s+''.join(chr(63+int(''.join(map(str,bits[i:i+6])),2)) for i in range(0,len(bits),6)))" $1 | nauty-labelg -q 2>/dev/null; }
for tag in a2_g96_17 a1_g96_31 a1_g96_51 a1_g96_66; do
  i=${tag##*_}; sol=$(cat records/d5D5_n384_$tag.sol)
  gap -q -c "ORDER:=96; ID:=$i; OUT:=\"$T/g\";" exh/gap_tab_gens.g > /dev/null
  python3 exh/lift_edges.py $T/g.txt "$sol" $T/gap.edges 2> /dev/null
  python3 records/build_lift_perm.py records/d5D5_n384_$tag.perm "$sol" $T/perm.edges 2> /dev/null
  a5=$($T/apsp $T/gap.edges 5 5 | tail -1); a4=$($T/apsp $T/gap.edges 5 4 | tail -1)
  b=$(python3 records/check_bfs.py $T/perm.edges 5 5 | sed 's/.*-> //')
  s=$(g6 records/d5D5_n384_$tag.edges); x=$(g6 $T/gap.edges); y=$(g6 $T/perm.edges)
  echo "$tag: GAP rebuild apsp D=5 [$a5], D=4 [$a4]; permutation rebuild BFS $b; isomorphic to saved: $([ "$s" = "$x" ] && echo yes || echo NO) / $([ "$s" = "$y" ] && echo yes || echo NO)"
done
rm -r $T
