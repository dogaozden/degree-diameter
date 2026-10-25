import random
lines = open('coll.txt').read().split('\n')
N = int(lines[0])
adj = [list(map(int, l.split())) for l in lines[1:N+1]]
best = 0
for trial in range(300):
    # min-degree greedy: pick vertex with fewest unblocked neighbours among unblocked
    blocked = [False]*N; deg = [30]*N; S = []
    alive = set(range(N))
    while alive:
        v = min(alive, key=lambda x: (deg[x], random.random())) if trial % 2 == 0 else random.choice(tuple(alive))
        S.append(v)
        rem = [v] + [u for u in adj[v] if u in alive]
        for x in rem:
            alive.discard(x)
            for y in adj[x]:
                if y in alive: deg[y] -= 1
    best = max(best, len(S))
    if trial % 50 == 0: print(trial, len(S), best, flush=True)
print("best independent set found", best)
