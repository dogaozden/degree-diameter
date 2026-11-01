import sys, random, time
sys.argv = ['x', '3', '0']
src = open('find_aut.py').read().split('found = {}')[0]
exec(src)
# depth profile of backtracking with budget
best = [0]
def run(r0, t0, budget):
    order, par = bfs_tree(r0)
    img = [-1]*N; used = [False]*N
    img[r0] = t0; used[t0] = True
    assigned = [r0]; nodes = [0]; deepest = [0]
    def rec(i):
        nodes[0] += 1
        if i > deepest[0]: deepest[0] = i
        if nodes[0] > budget: return False
        if i == N: return True
        v = order[i]
        cands = [c for c in adj[img[par[v]]] if not used[c]]
        random.shuffle(cands)
        for c in cands:
            if any(D[v][w] != D[c][img[w]] for w in assigned): continue
            img[v] = c; used[c] = True; assigned.append(v)
            if rec(i+1): return True
            assigned.pop(); used[c] = False; img[v] = -1
        return False
    ok = rec(1)
    return ok, nodes[0], deepest[0]
t = time.time()
print(run(0, 0, 20000), time.time()-t)
print(run(0, 1, 20000), time.time()-t)
print(run(0, 364, 20000), time.time()-t)
