"""c9: explicit graph builder for the test bed with freed sets R0 (lines, D->H t0 identity), R2 (points, H->D t2
identity) and free-form hubs.  Vertex ids: level j point p -> j*312+p ; level j line l -> j*312+156+l.
Matchings: t0 lvl0 line l <-> lvl1 line l ; t1 lvl1 point p <-> lvl2 line p (M1 = index map) ; t2 lvl2 point s <-> lvl0 point s.
Hub slots: alpha_c = lvl0 line c (B-hub side), beta_c = lvl1 line c (A-hub side), sigma_s = lvl2 point s (B side),
tau_s = lvl0 point s (A side).  B-hubs attach to alpha/sigma (colour class of lvl0 lines), A-hubs to beta/tau; Y joins them."""
import sys, os, subprocess
import numpy as np
sys.path.insert(0, '/home/user/degree-diameter/research/theorems/d5gq')
from gqlib import Q4
HERE = os.path.dirname(os.path.abspath(__file__))
G = Q4(5); NP, NL = G.np, G.nl; PER = NP + NL
BASE = []
for j in range(3):
    for l, pts in enumerate(G.lines):
        for p in pts: BASE.append((j*PER + p, j*PER + NP + l))
T0 = {l: (0*PER + NP + l, 1*PER + NP + l) for l in range(NL)}     # matching edge endpoints (lvl0 line, lvl1 line)
T1 = {p: (1*PER + p, 2*PER + NP + p) for p in range(NP)}          # (lvl1 point, lvl2 line)
T2 = {s: (2*PER + s, 0*PER + s) for s in range(NP)}                # (lvl2 point, lvl0 point)
MATCH = []
for l in range(NL): MATCH.append(T0[l])
for p in range(NP): MATCH.append(T1[p])
for s in range(NP): MATCH.append(T2[s])
ALPHA = lambda c: 0*PER + NP + c
BETA = lambda c: 1*PER + NP + c
SIGMA = lambda s: 2*PER + s
TAU = lambda s: 0*PER + s

def build_graph(R0, R2, Bhub_slots, Ahub_slots, Y, freedR1=()):
    """Bhub_slots: list (per hub) of list of ('a',c) / ('s',s); Ahub_slots likewise ('b',c) / ('t',s); Y: list (bi, ai)."""
    freed = set()
    E = []
    for (u, v) in BASE: E.append((u, v))
    # remove matching edges of freed elements
    removed = set()
    for c in R0: removed.add(T0[c])
    for s in R2: removed.add(T2[s])
    keep = [e for e in MATCH if e not in removed]
    E = BASE + keep
    nv = 3*PER
    nB = len(Bhub_slots); nA = len(Ahub_slots)
    hid = {}
    for h, slots in enumerate(Bhub_slots):
        for (kind, x) in slots:
            v = ALPHA(x) if kind == 'a' else SIGMA(x)
            E.append((nv + h, v))
    for g, slots in enumerate(Ahub_slots):
        for (kind, x) in slots:
            v = BETA(x) if kind == 'b' else TAU(x)
            E.append((nv + nB + g, v))
    for (h, g) in Y: E.append((nv + h, nv + nB + g))
    # drop isolated hubs by renumbering
    deg = np.zeros(nv + nB + nA, dtype=int)
    for u, v in E: deg[u] += 1; deg[v] += 1
    newid = {}
    k = 0
    for v in range(nv + nB + nA):
        if v < nv or deg[v] > 0:
            newid[v] = k; k += 1
    E2 = [(newid[u], newid[v]) for (u, v) in E]
    return k, E2, deg

def write(path, n, E):
    with open(path, 'w') as f:
        f.write('%d\n' % n)
        f.write('\n'.join('%d %d' % e for e in E)); f.write('\n')

def evaluate(n, E, tag):
    p = os.path.join(HERE, 'tmp_%s.txt' % tag)
    write(p, n, E)
    out = subprocess.run([os.path.join(HERE, 'badcount'), p, '5'], capture_output=True, text=True).stdout.split()
    return dict(maxdeg=int(out[1]), bad=int(out[5]))

def apsp_check(n, E, tag):
    p = os.path.join(HERE, 'tmp_%s.txt' % tag)
    write(p, n, E)
    return subprocess.run(['/home/user/degree-diameter/research/theorems/d5gq/apsp', p, '7', '5'], capture_output=True, text=True).stdout.strip().splitlines()[-1]
