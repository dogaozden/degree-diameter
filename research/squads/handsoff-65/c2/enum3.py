#!/usr/bin/env python3
"""Classes of 3x3 base multiplicity matrices (row/col sums 6, connected) up to row/col permutations.
Writes bases/class3_<k>.base (tabu format, p=3) and prints the class list."""
import itertools, os
p = 3
def rows(s):
    for a in range(s + 1):
        for b in range(s + 1 - a):
            c = s - a - b
            yield (a, b, c)
R = list(rows(6))
seen = set(); classes = []
def canon(M):
    best = None
    for pr in itertools.permutations(range(3)):
        for pc in itertools.permutations(range(3)):
            N = tuple(tuple(M[pr[i]][pc[j]] for j in range(3)) for i in range(3))
            if best is None or N < best:
                best = N
    return best
def connected(M):
    seen_v = {0}; st = [0]
    while st:
        x = st.pop()
        nb = [p + j for j in range(p) if M[x][j] > 0] if x < p else [i for i in range(p) if M[i][x - p] > 0]
        for y in nb:
            if y not in seen_v:
                seen_v.add(y); st.append(y)
    return len(seen_v) == 2 * p
for r1, r2, r3 in itertools.product(R, repeat=3):
    if any(r1[j] + r2[j] + r3[j] != 6 for j in range(3)):
        continue
    M = (r1, r2, r3)
    if not connected(M):
        continue
    c = canon(M)
    if c in seen:
        continue
    seen.add(c); classes.append(c)
os.makedirs("bases", exist_ok=True)
for k, M in enumerate(classes):
    edges = []
    for i in range(p):
        for j in range(p):
            edges += [(i, p + j)] * M[i][j]
    with open(f"bases/class3_{k}.base", "w") as f:
        f.write(f"{2*p} {len(edges)}\n" + " ".join(["0"] * p + ["1"] * p) + "\n")
        for u, w in edges:
            f.write(f"{u} {w} 0\n")
print(len(classes))
for k, M in enumerate(classes):
    print(k, M)
