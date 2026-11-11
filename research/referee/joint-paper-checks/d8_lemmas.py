"""Referee checks for Section 7: Lemma 7.10 on H(3) and H(4); Lemma 7.13 and the m2 bound of Fact 7.14 computed
from the definition of W_2 in Lemma 7.11; Lemma 7.17 on samples in Q(6,5)."""
import itertools, random
from collections import deque
from hexagon import Hex
def lemma710(q):
    H = Hex(q); N = H.N
    adj = [[N + k for k in H.lines_on[i]] for i in range(N)] + [list(H.lines[k]) for k in range(N)]
    dist = []
    for s in range(2 * N):
        d = [-1] * (2 * N); d[s] = 0; dq = deque([s])
        while dq:
            u = dq.popleft()
            for w in adj[u]:
                if d[w] < 0: d[w] = d[u] + 1; dq.append(w)
        dist.append(d)
    res = {}
    for t in random.sample(range(2 * N), 30):
        same = range(0, N) if t < N else range(N, 2 * N)
        opp = [w for w in range(2 * N) if dist[t][w] == 6]
        for z in same:
            dd = dist[t][z]
            b4 = sum(1 for w in opp if dist[z][w] <= 4); b2 = sum(1 for w in opp if dist[z][w] <= 2)
            res.setdefault(dd, set()).add((b4, b2))
    print(f"Lemma 7.10, q={q}: d(t,z) -> {{(|B(z,4)&opp(t)|, |B(z,2)&opp(t)|)}}: {dict(sorted(res.items()))}; q^4={q**4}, q^2={q*q}")
def classes_meeting(pos, typ):
    # Lemma 7.2 proof: (unbarred, barred) classes meeting the copy at position pos of a block of type typ
    if typ == 'a': return {(pos - 1) % 5, (pos + 1) % 5}, {(pos + 2) % 5, (pos + 3) % 5}
    return {(pos + 1) % 5, (pos + 2) % 5}, {(pos - 1) % 5, (pos + 1) % 5}
def C(k, bar, pattern):  # Definition 7.1
    out = set()
    for B, tp in enumerate(pattern):
        if not bar:
            offs = [-1, 1] if tp == 'a' else [3, 4]
        else:
            offs = [2, 3] if tp == 'a' else [-1, 1]
        for o in offs: out.add(5 * B + (k + o) % 5)
    return out
def fact714(alpha):
    worst_starved = 0; best_per_pattern = []; min_r4 = 10**9; lemma713 = True
    for pattern in itertools.product('ab', repeat=alpha):
        copies = range(5 * alpha)
        meet = {}
        for cpy in copies:
            B, i = divmod(cpy, 5); u, b = classes_meeting(i, pattern[B]); meet[cpy] = (u, b)
        # consistency with Definition 7.1
        for k in range(5):
            for bar in (0, 1):
                assert C(k, bar, pattern) == {c for c in copies if k in meet[c][bar]}
        share = lambda c1, c2, bar: bool(meet[c1][bar] & meet[c2][bar])
        best = None
        for bar in (0, 1):
            for k in range(5):
                CX = C(k, bar, pattern); other = 1 - bar
                for cp in copies:
                    if cp in CX: continue
                    Nx = {c1 for c1 in CX if share(c1, cp, other)}
                    r4 = len(Nx); min_r4 = min(min_r4, r4)
                    if r4 != alpha: continue
                    W2 = set()
                    for c1 in CX:
                        for c2 in copies:
                            if c2 in (c1, cp): continue
                            if share(c2, c1, bar) and share(c2, cp, other): W2.add((cp, c2))      # kind 1
                            if share(c2, c1, other) and share(c2, cp, other): W2.add((cp, c1))    # kind 2
                            if share(c2, c1, other) and share(c2, cp, bar): W2.add((c2, c1))      # kind 3
                    W2 = {pr for pr in W2 if pr[0] != pr[1]}
                    m2 = len([pr for pr in W2 if not (pr[0] == cp and pr[1] in Nx)])
                    worst_starved = max(worst_starved, m2)
                    best = m2 if best is None else min(best, m2)
        # Lemma 7.13: the stated starved pairs
        for k in range(5):
            if 'a' in pattern:
                Bp = pattern.index('a'); cp = 5 * Bp + (k + 3) % 5
            else:
                cp = 5 * 0 + k % 5
            CX = C(k, 0, pattern)
            lemma713 &= cp not in CX and len({c1 for c1 in CX if share(c1, cp, 1)}) == alpha
            if 'b' in pattern:
                Bp = pattern.index('b'); cp = 5 * Bp + (k + 3) % 5
            else:
                cp = (k + 1) % 5
            CX = C(k, 1, pattern)
            lemma713 &= cp not in CX and len({c1 for c1 in CX if share(c1, cp, 0)}) == alpha
        best_per_pattern.append(best)
    print(f"alpha={alpha}: min r4 over all pairs {min_r4}; Lemma 7.13 pairs starved: {lemma713}; max m2 over starved pairs {worst_starved};"
          f" max over patterns of the best starved m2: {max(best_per_pattern)}; 8a^2-1={8*alpha*alpha-1}")
def lemma717(q, trials=300):
    H = Hex(q); pts = H.pts; N = H.N; b = H.b
    perp = lambda i, j: b(pts[i], pts[j]) == 0
    viol = 0; mn = 10**9
    for _ in range(trials):
        y, y2, t = random.sample(range(N), 3)
        inter = [w for w in range(N) if perp(w, y) and perp(w, y2) and not perp(w, t)]
        online = perp(y, y2) and t in H.span_pts_idx(y, y2) if hasattr(H, 'span_pts_idx') else None
        if perp(y, y2):
            L = {H.pid[p] for p in H.span_pts(pts[y], pts[y2])}
            if t in L:
                viol += len(inter) != 0; continue
        mn = min(mn, len(inter))
    print(f"Lemma 7.17(a), q={q}: {trials} random triples; violations of 'empty' case {viol}; min size otherwise {mn} (q^3-q={q**3-q})")
if __name__ == '__main__':
    random.seed(2)
    lemma710(3); lemma710(4)
    for a in [3, 4, 5, 6, 7, 8]: fact714(a)
    lemma717(3); lemma717(5, 200)
