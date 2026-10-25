# Orbit union search for non-collinear sets of H(9) under a subgroup G of SL(3,9) (optionally with Frobenius).
# usage: orbits.py GROUP FROB(0|1) TIMELIMIT
# Orbits of <G, sigma> on the 66,430 points; self-compatible orbits (no two points collinear); compatibility
# between orbits = no point of one collinear with a point of the other; max-weight clique (weight = orbit size)
# by branch and bound with a colouring bound (time limited). Writes best_<GROUP>_<F>.txt (plain point ids).
import sys, time, pickle
import numpy as np
sys.path.insert(0, '/home/user/degree-diameter/research/squads/d10D7-r6/c6')
from h9 import *

GROUP = sys.argv[1]; WITHF = int(sys.argv[2]); TL = float(sys.argv[3])
G = pickle.load(open('/home/user/degree-diameter/research/squads/d10D7-r6/c6/groups.pkl', 'rb'))
t0 = time.time()
perms = [perm_of(g) for g in G[GROUP]]
if WITHF: perms.append(perm_frob())
for p in perms: assert lines_ok(p), 'generator does not preserve lines'
lab = orbit_labels(perms)
M = int(lab.max()) + 1
sizes = np.bincount(lab, minlength=M)
# self-conflict: a point collinear with another point of its own orbit
selfc = (lab[NB] == lab[:, None]).any(axis=1)
bad = np.zeros(M, bool); bad[lab[selfc]] = True
S = np.nonzero(~bad)[0]
# conflict matrix over all orbits (conflict(i,j) iff some point of i collinear with some point of j)
CF = np.zeros((M, M), bool)
CF[np.repeat(lab, 90), lab[NB].ravel()] = True
CF = CF | CF.T
np.fill_diagonal(CF, False)
n = len(S)
print('group %s frob %d: orbits %d, size distribution %s, self-compatible orbits %d, sizes %s  [%.1fs]' % (
    GROUP, WITHF, M, dict(zip(*np.unique(sizes, return_counts=True))) if M < 10**6 else '', n,
    sorted(set(sizes[S].tolist())), time.time() - t0), flush=True)
if n == 0:
    print('RESULT %s %d best 0' % (GROUP, WITHF)); sys.exit(0)
CS = CF[np.ix_(S, S)]
ADJ = [0] * n                       # compatibility graph as bitsets
for i in range(n):
    row = ~CS[i]; row[i] = False
    b = 0
    for j in np.nonzero(row)[0].tolist(): b |= (1 << j)
    ADJ[i] = b
W = sizes[S].tolist()

def greedy_clique(order):
    cl = []; cand = (1 << n) - 1
    for v in order:
        if (cand >> v) & 1:
            cl.append(v); cand &= ADJ[v]
    return cl

def bits(x):
    out = []
    while x:
        lb = x & -x; out.append(lb.bit_length() - 1); x ^= lb
    return out

best = {'w': 0, 'set': [], 'exact': True}
# greedy lower bound from several weight orders
for order in [sorted(range(n), key=lambda i: -W[i]), sorted(range(n), key=lambda i: -(W[i] * bin(ADJ[i]).count('1')))]:
    cl = greedy_clique(order); wcl = sum(W[i] for i in cl)
    if wcl > best['w']: best = {'w': wcl, 'set': cl, 'exact': True}
print('greedy lower bound', best['w'], flush=True)

def colour_order(P):
    """greedy colouring of candidate set P (bitset): classes are sets of pairwise conflicting vertices.
    returns vertices in colour order with cumulative bound."""
    seq = []; bound = []; total = 0
    R = P
    while R:
        cls = []; Q = R; mx = 0
        while Q:
            lb = Q & -Q; v = lb.bit_length() - 1
            cls.append(v); mx = max(mx, W[v])
            Q &= ~ADJ[v]; Q &= ~lb
            R &= ~lb
        total += mx
        for v in cls:
            seq.append(v); bound.append(total)
    return seq, bound

nodes = [0]
def expand(P, cw, cur):
    nodes[0] += 1
    if time.time() - t0 > TL:
        best['exact'] = False; return
    if cw > best['w']:
        best['w'] = cw; best['set'] = list(cur)
    if not P: return
    seq, bound = colour_order(P)
    for k in range(len(seq) - 1, -1, -1):
        if cw + bound[k] <= best['w']: return
        v = seq[k]
        expand(P & ADJ[v], cw + W[v], cur + [v])
        if time.time() - t0 > TL:
            best['exact'] = False; return
        P &= ~(1 << v)

expand((1 << n) - 1, 0, [])
ids = []
for i in best['set']:
    ids += np.nonzero(lab == S[i])[0].tolist()
ids = sorted(ids)
ok = no_two_collinear(ids)
print('RESULT group %s frob %d: best union %d points (%d orbits, orbit sizes %s), exact=%s, nodes %d, noncollinear=%s [%.1fs]' % (
    GROUP, WITHF, len(ids), len(best['set']), sorted([W[i] for i in best['set']], reverse=True),
    best['exact'], nodes[0], ok, time.time() - t0), flush=True)
fn = '/home/user/degree-diameter/research/squads/d10D7-r6/c6/best_%s_F%d.txt' % (GROUP.replace(':', ''), WITHF)
open(fn, 'w').write('\n'.join(map(str, ids)) + '\n')
print('wrote', fn, len(ids), flush=True)
