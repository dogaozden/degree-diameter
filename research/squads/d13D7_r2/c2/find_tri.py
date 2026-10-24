# list nonsingular directions tangent (rank-1 plane) to u1 and find pairwise-tangent triples (card c2)
import itertools, sys
q = 11
def Q(x): a,b,c,e,f = x; return (c*c - a*e - b*f) % q
def P(x, y):
    a,b,c,e,f = x; A,B,C,E,F = y
    return (2*c*C - (a*E + A*e) - (b*F + B*f)) % q
def normalize(x):
    for k in x:
        if k % q:
            inv = pow(k, q-2, q); return tuple((v*inv) % q for v in x)
    return None
dirs = set()
for x in itertools.product(range(q), repeat=5):
    if any(x):
        n = normalize(x)
        if n: dirs.add(n)
dirs = sorted(dirs)
print('directions', len(dirs))
u1 = (1,0,0,9,0)
def tangent(u, w):
    return P(u, w)**2 % q == (4*Q(u)*Q(w)) % q and Q(u) and Q(w)
T1 = [w for w in dirs if tangent(u1, w) and w != u1]
print('tangent to u1 (nonsingular, excluding u1):', len(T1), 'classes of Q:', sorted(set(Q(w) for w in T1)))
best = None
for w in T1[:400]:
    for z in T1:
        if z <= w: continue
        if tangent(w, z):
            best = (w, z); break
    if best: break
print('triple example u1, w, z:', u1, best)
import pickle
pickle.dump((T1, best), open('find_tri.pkl', 'wb'))
