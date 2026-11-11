# builds cubic bipartite bases from LCF notation, relabelled so A = even cycle positions = [0,h), B = [h,2h)
import sys, collections
def lcf(pat, reps):
    b = len(pat) * reps
    adj = collections.defaultdict(set)
    for i in range(b):
        j = (i + 1) % b; adj[i].add(j); adj[j].add(i)
    for i in range(b):
        k = pat[i % len(pat)]; j = (i + k) % b
        if j in adj[i]: continue
        assert j != i
        adj[i].add(j); adj[j].add(i)
    return b, adj
def write(name, b, adj):
    h = b // 2
    lab = {}
    for i in range(b):
        lab[i] = i // 2 if i % 2 == 0 else h + i // 2
    edges = set()
    for i in range(b):
        for j in adj[i]:
            if i % 2 == 0:
                edges.add((lab[i], lab[j]))
    assert all(len(adj[i]) == 3 for i in range(b))
    with open(name, 'w') as f:
        f.write(f"{b}\n")
        for u, v in sorted(edges): f.write(f"{u} {v}\n")
    print(name, b, len(edges))
pappus = ([5, 7, -7, 7, -7, -5], 3)
tutte8 = ([-13, -9, 7, -7, 9, 13], 5)
for nm, (pat, r) in [("pappus", pappus), ("tutte8", tutte8)]:
    b, adj = lcf(pat, r)
    write(f"bases/{nm}.txt", b, adj)
