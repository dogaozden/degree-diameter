# chart-independent check: same-side pairs of the CONTROLLER at distance > 4 (no lift walk of length <= 4 can exist)
import sys, collections
def check(fn):
    E = [tuple(map(int, l.split())) for l in open(fn) if l.strip()]
    m = max(a for a, b, e in E) + 1
    adj = {('A', a): [] for a in range(m)}; adj.update({('B', b): [] for b in range(m)})
    for a, b, e in E:
        adj[('A', a)].append(('B', b)); adj[('B', b)].append(('A', a))
    bad = collections.Counter(); worst = 0
    for side in 'AB':
        for s in range(m):
            dist = {('A' if side == 'A' else 'B', s): 0}
            q = collections.deque([(('A' if side == 'A' else 'B', s))])
            while q:
                x = q.popleft()
                for y in adj[x]:
                    if y not in dist: dist[y] = dist[x] + 1; q.append(y)
            for v in range(m):
                if v == s: continue
                d = dist.get((side, v), 99)
                if d > 4: bad[side] += 1
                if d > worst and d < 99: worst = d
    return m, dict(bad), worst
for fn in sys.argv[1:]:
    m, bad, worst = check(fn)
    print(fn.split('/')[-1], 'm =', m, '| same-side ordered pairs at controller distance > 4:', bad, '| max finite same-side distance:', worst)
