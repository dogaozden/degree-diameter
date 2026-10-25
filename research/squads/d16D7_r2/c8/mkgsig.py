# <g,sigma>-invariant quotient of the orbit graphs: super-vertices = sigma-orbits of og vertices (valid ones)
import numpy as np, sys, pickle
sys.path.insert(0, '/home/user/degree-diameter/research/squads/d16D7_r2/c8')
from load import *
from collections import defaultdict
kind = sys.argv[1]
q, N, L, LP, X = load_hex()
sm = pickle.load(open('sigma_mat.pkl', 'rb')); S, Sinv = sm['S'], sm['Sinv']
def normalise1(V):
    V = V % 13
    lead = np.argmax(V != 0, axis=1)
    inv = np.array([0] + [pow(a, 11, 13) for a in range(1, 13)], dtype=np.int64)
    s = inv[V[np.arange(len(V)), lead]]
    return (V * s[:, None]) % 13
code = X @ (13 ** np.arange(7)); order = np.argsort(code); sc = code[order]
def sig_points(pts):
    Xp = X[pts]
    Y = np.zeros((len(pts), 7), dtype=np.int64)
    Y[:, 0:3] = (Xp[:, 0:3] @ S.T) % 13; Y[:, 3] = Xp[:, 3]; Y[:, 4:7] = (Xp[:, 4:7] @ Sinv) % 13
    Y = normalise1(Y); yc = Y @ (13 ** np.arange(7))
    pos = np.searchsorted(sc, yc); assert np.all(sc[np.minimum(pos, len(sc)-1)] == yc)
    return order[pos]
keyd = {tuple(sorted(r)): i for i, r in enumerate(LP.tolist())}
def sig_lines(lines):
    img = sig_points(LP[lines].ravel()).reshape(len(lines), 14)
    return np.array([keyd[tuple(sorted(r))] for r in img.tolist()])
M, E, rep, nb = load_og(D + ('og_lines.txt' if kind == 'sp' else 'og_pts.txt'))
gof = np.load('orbit_lines.npy' if kind == 'sp' else 'orbit_pts.npy')
vid = {int(gof[rep[i]]): i for i in range(M)}
if kind == 'sp':
    img_el = sig_lines(rep)
else:
    img_el = sig_points(rep)
tau = np.array([vid[int(gof[e])] for e in img_el])
# check tau is a permutation of vertices and preserves adjacency
assert len(set(tau.tolist())) == M
adjset = [set(x.tolist()) for x in nb]
ok = all(set(tau[u] for u in adjset[i]) == adjset[tau[i]] for i in range(M))
print(kind, 'tau permutation ok; preserves og adjacency:', ok, flush=True)
seen = np.zeros(M, bool); supers = []
for i in range(M):
    if seen[i]: continue
    orb = [i]; j = int(tau[i])
    while j != i:
        orb.append(j); j = int(tau[j])
    for x in orb: seen[x] = True
    # valid if members pairwise non-adjacent
    if any(b in adjset[a] for a in orb for b in orb if a != b): continue
    supers.append(orb)
cnt = defaultdict(int)
for s in supers: cnt[len(s)] += 1
print(kind, 'valid super-vertices', len(supers), 'sizes', dict(cnt), flush=True)
member_of = {}
for si, s in enumerate(supers):
    for x in s: member_of[x] = si
nbs = [set() for _ in supers]
for si, s in enumerate(supers):
    for x in s:
        for u in adjset[x]:
            if u in member_of and member_of[u] != si:
                nbs[si].add(member_of[u])
with open(f'wgs_{kind}.txt', 'w') as f:
    f.write(f'{len(supers)}\n')
    for si, s in enumerate(supers):
        l = sorted(nbs[si])
        f.write(f'{len(s)} {len(l)} ' + ' '.join(map(str, l)) + '\n')
pickle.dump(supers, open(f'gsupers_{kind}.pkl', 'wb'))
print(kind, 'avg deg', round(sum(len(x) for x in nbs)/len(nbs), 1))
