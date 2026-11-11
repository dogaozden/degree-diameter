# Convert a regular bipartite graph (edge list) into the fitq controller format: decompose into d perfect matchings,
# sigma_a: A -> M1, B -> M2 ; sigma_b: A -> M3, B -> M4 (d = 4). usage: tomatchings.py EDGES OUT
import sys, collections
E = [tuple(map(int, l.split())) for l in open(sys.argv[1]) if l.strip() and not l.startswith('#') and len(l.split()) == 2]
adj = collections.defaultdict(set)
for a, b in E: adj[a].add(b); adj[b].add(a)
V = sorted(adj); n = len(V)
col = {V[0]: 0}; st = [V[0]]
while st:
    x = st.pop()
    for y in adj[x]:
        if y not in col: col[y] = 1 - col[x]; st.append(y)
A = [v for v in V if col[v] == 0]; B = [v for v in V if col[v] == 1]
assert len(A) == len(B) and all(len(adj[v]) == 4 for v in V)
idA = {v: i for i, v in enumerate(A)}; idB = {v: i for i, v in enumerate(B)}
rem = {a: set(adj[a]) for a in A}
def matching():
    mate = {}
    def aug(a, seen):
        for b in rem[a]:
            if b in seen: continue
            seen.add(b)
            if b not in mate or aug(mate[b], seen):
                mate[b] = a; return True
        return False
    for a in A:
        assert aug(a, set())
    return {a: b for b, a in mate.items()}
Ms = []
for _ in range(4):
    M = matching(); Ms.append(M)
    for a, b in M.items(): rem[a].discard(b)
nA = len(A); sa = [0] * n; sb = [0] * n
for a in A:
    sa[idA[a]] = nA + idB[Ms[0][a]]; sb[idA[a]] = nA + idB[Ms[2][a]]
for a in A:
    sa[nA + idB[Ms[1][a]]] = idA[a]; sb[nA + idB[Ms[3][a]]] = idA[a]
open(sys.argv[2], 'w').write(f'{n} {nA}\n' + ' '.join(map(str, sa)) + '\n' + ' '.join(map(str, sb)) + '\n')
print('n', n, 'nA', nA)
