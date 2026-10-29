#!/usr/bin/env python3
"""Hub graphs by sums of hexagons (D7_THEOREMS.md, Lemma 4.2 and Theorem 4.4).

HG(K1, K2; delta): bipartite, colour classes of sizes K1, K2, maximum degree <= delta, same-colour distances <= 6.

Parts (each with colour classes (A_i, B_i)):
  * core (s, c): the incidence graph of H(s) with every point and every line replaced by 1..c copies (blow-up,
    Lemma 4.1); sizes |A_i|, |B_i| anywhere in [K0(s), c K0(s)], degree <= c(s+1), diameter 6 (every pair, both
    colours: same colour <= 6, different colours <= 5);
  * last part (optional): the plane with pendant trees of D7_HEXAGON.md Lemma 7.1 (two colours sized independently),
    sizes in [7, kappa(delta_L)], degree <= delta_L, same-colour distances <= 6.
Sum (Lemma 4.2): parts Y_1..Y_r in order, the last one possibly a pendant-tree part; for every i < j an injective map
A_j -> B_i and B_j -> A_i (edges).  Needs |A_j| <= |B_i| and |B_j| <= |A_i| for i < j.  Degree <= max deg(Y_i) + r - 1.

For every k and every prime power q <= QMAX not covered by Lemma 4.1 alone (hubcap.py), search for a sum with r <= RMAX
parts.  Output: hubsum.out with one certificate per (q, k) (the parts and their sizes), and the uncovered (q, k).
A certificate is checked by verify(): sizes add up, ordering, degrees."""
import sys, signal
from hubcap_lib import PP, K0, slots, kappa_tab, tree_ok

QMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 200
RMAX = 7

def core_range(s, c):
    return K0(s), c * K0(s)

def search(K1, K2, d):
    """return a list of parts [('core', s, c, x, y) ..., ('tree', dL, x, y)] or None"""
    kap = kappa_tab(d)
    best = None
    def dfs(parts, R1, R2, smax, maxdeg):
        nonlocal best
        rr = len(parts)
        rmax = min(RMAX, d - maxdeg + 1) if parts else RMAX   # final number of parts allowed by the degrees so far
        if rr > rmax:
            return
        if R1 == 0 and R2 == 0 and rr >= 1:
            if check_deg(parts, d) and check_order(parts):
                best = list(parts)
            return
        dL = d - rr                                            # a tree part as part rr+1: its degree + rr <= d
        if rr + 1 <= rmax and dL >= 2 and R1 >= 7 and R2 >= 7 and tree_ok(R1, R2, dL):
            cand = parts + [('tree', dL, R1, R2)]
            if check_deg(cand, d) and check_order(cand):
                best = cand; return
        if rr + 1 > rmax:
            return
        # capacity bound: every later part has at most cmax*K0(s) <= max over s of that, plus the tree part
        cands = []
        for s in PP:
            if s > smax or s + 1 + rr > d: break
            k0 = K0(s)
            if k0 > min(R1, R2): break
            cmax = (d - rr) // (s + 1)
            cands.append((s, k0, cmax))
        if not cands:
            return
        cap = max(cm * k0 for (s, k0, cm) in cands)
        if (rmax - rr) * cap + kap[max(2, d - rr)] < max(R1, R2):
            return
        for (s, k0, cmax) in reversed(cands):
            for c in range(1, cmax + 1):
                x = min(R1, c * k0); y = min(R2, c * k0)
                dfs(parts + [('core', s, c, x, y)], R1 - x, R2 - y, s, max(maxdeg, c * (s + 1)))
                if best is not None:
                    return
                if c * k0 >= max(R1, R2):
                    break
    dfs([], K1, K2, PP[-1], 0)
    return best

def part_deg(p):
    return p[2] * (p[1] + 1) if p[0] == 'core' else p[1]
def check_deg(parts, d):
    r = len(parts)
    return all(part_deg(p) + r - 1 <= d for p in parts)
def sizes(p):
    return (p[3], p[4]) if p[0] == 'core' else (p[2], p[3])
def check_order(parts):
    for i in range(len(parts)):
        for j in range(i + 1, len(parts)):
            ai, bi = sizes(parts[i]); aj, bj = sizes(parts[j])
            if aj > bi or bj > ai:
                return False
    return True
def verify(parts, K1, K2, d):
    assert sum(sizes(p)[0] for p in parts) == K1 and sum(sizes(p)[1] for p in parts) == K2
    assert check_deg(parts, d) and check_order(parts)
    for p in parts:
        if p[0] == 'core':
            lo, hi = core_range(p[1], p[2]); assert lo <= p[3] <= hi and lo <= p[4] <= hi
        else:
            assert tree_ok(p[2], p[3], p[1])
    return True

def _timeout(*a):
    raise TimeoutError

if __name__ == '__main__':
    out = open('hubsum.out', 'w')
    def say(*a):
        s = ' '.join(str(x) for x in a); print(s); out.write(s + '\n'); out.flush()
    say('Lemma 4.2 certificates (first-found search; superseded by hubopt.py) (sum of blown-up hexagons and a pendant-tree part), prime powers q <= %d, r <= %d' % (QMAX, RMAX))
    for k in range(1, 13):
        unc = []
        for q in PP:
            if q > QMAX: break
            d = q - k
            if d < 2: continue
            KB, KA = slots(q, k)
            signal.signal(signal.SIGALRM, _timeout); signal.alarm(120)
            try:
                sol = search(KB, KA, d)
            except TimeoutError:
                sol = None; say('k=%d q=%d: search stopped after 120 s' % (k, q))
            signal.alarm(0)
            if sol is None:
                unc.append(q); continue
            verify(sol, KB, KA, d)
            say('k=%d q=%d delta=%d K_B=%d K_A=%d: %s' % (k, q, d, KB, KA,
                ' + '.join('H(%d)x%d[%d,%d]' % (p[1], p[2], p[3], p[4]) if p[0] == 'core' else 'tree(delta=%d)[%d,%d]' % (p[1], p[2], p[3]) for p in sol)))
        say('k=%d: NOT covered: %s' % (k, unc))
