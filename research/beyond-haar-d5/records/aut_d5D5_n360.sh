#!/bin/bash
# Automorphism group of the 360-vertex (5,5) graph: nauty (dreadnaut) for generators, GAP for structure.
# Run from research/beyond-haar-d5. Output: records/d5D5_n360_aut.txt
E=records/d5D5_n360_lift_g90_6.edges; T=$(mktemp -d)
python3 - "$E" > $T/g.dre <<'PY'
import sys
L=open(sys.argv[1]).read().split('\n'); n=int(L[0]); adj=[[] for _ in range(n)]
for l in L[1:]:
    if l.strip(): a,b=map(int,l.split()); adj[a].append(b)
print(f"$=0 n={n} g"); print(";\n".join(f"{v}: "+" ".join(map(str,adj[v])) for v in range(n))+"."); print("x")
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
Read("$T/gens.g"); A:=Group(gens);
Print("|Aut| = ", Size(A), " = ", StructureDescription(A), ", IdGroup ", IdGroup(A), "\n");
for o in Orbits(A,[1..360]) do Print("orbit of size ", Length(o), ": base fibres ", Set(List(o, v -> QuoInt(v-1, 90))), " (0 A0, 1 A1, 2 B0, 3 B1)\n"); od;
C:=Stabilizer(A, [1..180], OnSets);
Print("colour-preserving part: order ", Size(C), " = ", StructureDescription(C), ", orbit sizes ", List(Orbits(C,[1..360]), Length), "\n");
QUIT;
GG
{ grep grpsize $T/g.aut; gap -q $T/a.g < /dev/null; } | tee records/d5D5_n360_aut.txt
rm -r $T
