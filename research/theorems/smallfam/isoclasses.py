"""Isomorphism classes (igraph/BLISS canonical form) of Haar graphs H(G,S) for the solutions of an hx run on a group
given by a multiplication table.  Usage: python3 isoclasses.py TABLE SOLFILE"""
import sys, hashlib
import igraph as ig
tab = open(sys.argv[1]).read().split('\n')
N, e = map(int, tab[0].split())
T = [list(map(int, tab[1 + x].split())) for x in range(N)]
sols = [list(map(int, l.split()[1:])) for l in open(sys.argv[2]) if l.startswith('SOL')]
classes = {}
for S in sols:
    E = [(g, N + T[s][g]) for g in range(N) for s in S]
    G = ig.Graph(n=2 * N, edges=E)
    perm = G.canonical_permutation()
    H = G.permute_vertices(perm)
    key = hashlib.sha256(str(sorted(tuple(sorted(x)) for x in H.get_edgelist())).encode()).hexdigest()[:16]
    if key not in classes:
        classes[key] = (S, G.girth(), G.count_automorphisms())
    else:
        pass
    classes[key] = classes[key] if key in classes else None
print(f'{len(sols)} solutions -> {len(classes)} isomorphism classes')
for k, (S, gi, aut) in classes.items():
    print(f'class {k}: first S {S} girth {gi} |Aut| {aut}')
