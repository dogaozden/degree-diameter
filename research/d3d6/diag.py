"""List vertex pairs at distance > 3 for given frames.  python3 diag.py q frames.json"""
import json, sys
from collections import deque, Counter
from multi_gadget import C, gadget_incidences


def far_pairs(lines, frames):
    inc = gadget_incidences(lines, frames)
    pts = sorted({a for a, b in inc}, key=str); lns = sorted({b for a, b in inc}, key=str)
    V = pts + lns; ids = {v: i for i, v in enumerate(V)}
    adj = [[] for _ in V]
    for a, b in inc:
        adj[ids[a]].append(ids[b]); adj[ids[b]].append(ids[a])
    bad = []
    for s in range(len(V)):
        d = [-1] * len(V); d[s] = 0; dq = deque([s])
        while dq:
            u = dq.popleft()
            if d[u] == 3: continue
            for w in adj[u]:
                if d[w] < 0: d[w] = d[u] + 1; dq.append(w)
        for t in range(s + 1, len(V)):
            if d[t] < 0: bad.append((V[s], V[t]))
    return bad


if __name__ == '__main__':
    q = int(sys.argv[1]); frames = json.load(open(sys.argv[2]))
    pts, lines = C.pg_plane(q)
    bad = far_pairs(lines, [tuple(f) for f in frames])
    print(len(bad)); [print(b) for b in bad[:40]]
