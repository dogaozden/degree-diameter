#!/bin/bash
# usage: aut_haar.sh EDGES   (bipartite graph, first half of the vertices on one side as in our lift/coset edge lists
# when SIDE_SPLIT is not given: the colour classes are computed by BFS)
# nauty (dreadnaut) for Aut generators, GAP for: |Aut|, structure, vertex orbits, the colour-preserving part C, and the
# Haar test: a Haar graph on 2N vertices needs a subgroup of C of order N acting regularly on each colour class.
E=$1; T=$(mktemp -d)
python3 - "$E" $T/side.g > $T/g.dre <<'PY'
import sys
from collections import deque
L=open(sys.argv[1]).read().split('\n'); n=int(L[0]); adj=[[] for _ in range(n)]
for l in L[1:]:
    if l.strip(): a,b=map(int,l.split()); adj[a].append(b); adj[b].append(a)
col=[-1]*n; col[0]=0; q=deque([0])
while q:
    x=q.popleft()
    for y in adj[x]:
        if col[y]<0: col[y]=1-col[x]; q.append(y)
open(sys.argv[2],'w').write("SIDE0:=["+",".join(str(v+1) for v in range(n) if col[v]==0)+"];; NV:="+str(n)+";;\n")
print(f"$=0 n={n} g"); print(";\n".join(f"{v}: "+" ".join(map(str,[w for w in adj[v] if w>v])) for v in range(n))+"."); print("x")
PY
dreadnaut < $T/g.dre > $T/g.aut
python3 - $T/g.aut > $T/gens.g <<'PY'
import re, sys
gens=[]
for line in open(sys.argv[1]):
    if line.startswith('('): gens.append(line.strip())
    elif line.startswith('   ') and gens and not line.strip().startswith('level'): gens[-1]+=' '+line.strip()
print('gens:=['+','.join(''.join('('+','.join(str(int(x)+1) for x in c.split())+')' for c in re.findall(r'\(([^)]*)\)', g)) for g in gens)+'];')
PY
cat > $T/a.g <<GG
Read("$T/gens.g"); Read("$T/side.g"); A:=Group(gens); N:=NV/2;
Print("|Aut| = ", Size(A), ", structure ", StructureDescription(A), "\n");
Print("vertex orbits: ", List(Orbits(A,[1..NV]), Length), "\n");
C:=Stabilizer(A, SIDE0, OnSets);
Print("colour-preserving part C: order ", Size(C), " = ", StructureDescription(C), ", orbit sizes ", List(Orbits(C,[1..NV]), Length), "\n");
if Size(C) mod N <> 0 then Print("HAAR: no (|C| is not divisible by ", N, ")\n");
else
  cand := Filtered(List(ConjugacyClassesSubgroups(C), Representative), R -> Size(R) = N);
  reg := Filtered(cand, R -> Length(Orbits(R, [1..NV])) = 2);
  Print("subgroups of C of order ", N, " (up to conjugacy): ", Length(cand), "; transitive on both sides: ", Length(reg), "\n");
  if Length(reg) = 0 then Print("HAAR: no\n"); else Print("HAAR: yes, R = ", StructureDescription(reg[1]), "\n"); fi;
fi;
QUIT;
GG
{ echo "graph $E"; grep grpsize $T/g.aut; gap -q $T/a.g < /dev/null; }
rm -r $T
