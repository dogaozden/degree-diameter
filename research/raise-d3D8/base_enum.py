#!/usr/bin/env python3
"""Connected 3-regular bipartite multigraphs on 2k vertices (A = 0..k-1, B = k..2k-1), up to relabelling.
A cubic bipartite multigraph is a multiset of 3 perfect matchings, i.e. 3 permutations sigma_i of range(k) (edge a -- k+sigma_i(a)).
Writes bases/b{2k}_{idx}.txt in lift_ex format.  Usage: base_enum.py k"""
import sys, itertools, os

def canon(sig, k):
    best = None
    for pi in itertools.permutations(range(k)):
        pinv = [0] * k
        for i, x in enumerate(pi):
            pinv[x] = i
        for rho in itertools.permutations(range(k)):
            new = []
            for s in sig:
                # a -> rho(s(pinv(a)))  (relabel A by pinv, B by rho)
                new.append(tuple(rho[s[pinv[a]]] for a in range(k)))
            key = tuple(sorted(new))
            if best is None or key < best:
                best = key
    return best

def connected(sig, k):
    adj = {v: set() for v in range(2 * k)}
    for s in sig:
        for a in range(k):
            adj[a].add(k + s[a]); adj[k + s[a]].add(a)
    seen = {0}; st = [0]
    while st:
        x = st.pop()
        for y in adj[x]:
            if y not in seen:
                seen.add(y); st.append(y)
    return len(seen) == 2 * k

if __name__ == "__main__":
    k = int(sys.argv[1]); b = 2 * k
    perms = list(itertools.permutations(range(k)))
    classes = set()
    for combo in itertools.combinations_with_replacement(perms, 3):
        if connected(combo, k):
            classes.add(canon(combo, k))
    os.makedirs("bases", exist_ok=True)
    for idx, sig in enumerate(sorted(classes)):
        edges = [(a, k + s[a]) for s in sig for a in range(k)]
        with open(f"bases/b{b}_{idx}.txt", "w") as f:
            f.write(f"{b} {len(edges)}\n")
            for x, y in edges:
                f.write(f"{x} {y}\n")
        print(f"bases/b{b}_{idx}.txt", sig)
    print("classes", len(classes))
