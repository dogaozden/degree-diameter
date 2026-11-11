# summ.py FAMILY: summary of out/FAMILY_scanA.tsv (A-root part per class) and out/FAMILY_scanB.tsv (B-root part, optional)
# members = double cosets; a class of orbit size w stands for w members with identical cost.
# C (full cost, plain vertices) = uBA + uAA + uBB. Exact for self-inverse classes (uBB = uAA) and for classes with a
# B line; otherwise C >= P = uBA + uAA (lower bound).
import sys, os, bisect
fam = sys.argv[1]
base = os.path.dirname(os.path.abspath(__file__)) + '/out/'
A = {}
for line in open(base + fam + '_scanA.tsv'):
    t = line.split()
    if t[0] != 'A': continue
    A[int(t[1])] = dict(orb=int(t[2]), sym=int(t[3]), uBA=int(t[4]), uAA=int(t[5]), z=tuple(map(int, t[6:10])))
B = {}
if os.path.exists(base + fam + '_scanB.tsv'):
    for line in open(base + fam + '_scanB.tsv'):
        t = line.split()
        if t[0] == 'B': B[int(t[1])] = int(t[2])
nmem = sum(a['orb'] for a in A.values())
print(f"{fam}: classes scanned {len(A)} of {'16293' if fam=='K' else '16407'}, members covered {nmem}, B-root known for {len(B)} classes")
def wq(vals, q):      # weighted quantile over (value, weight) list sorted by value
    tot = sum(w for _, w in vals); acc = 0
    for v, w in vals:
        acc += w
        if acc >= q * tot: return v
    return vals[-1][0]
P = sorted(((a['uBA'] + a['uAA'], a['orb']) for a in A.values()))
print("P = uBA+uAA (lower bound of C) over scanned members: min %d p0.1 %d p1 %d p10 %d median %d" % (
    P[0][0], wq(P, .001), wq(P, .01), wq(P, .10), wq(P, .5)))
ex = []; lb = []
for cid, a in A.items():
    if a['sym']: ex.append((a['uBA'] + 2 * a['uAA'], a['orb'], cid))
    elif cid in B: ex.append((a['uBA'] + a['uAA'] + B[cid], a['orb'], cid))
    else: lb.append((a['uBA'] + a['uAA'], a['orb'], cid))
nex = sum(w for _, w, _ in ex); print(f"exact full C known for {len(ex)} classes = {nex} members (self-inverse: {sum(1 for c in A if A[c]['sym'])} classes)")
ex.sort()
if ex:
    C = sorted(((c, w) for c, w, _ in ex))
    print("exact C over known members: min %d p0.1 %s p1 %s" % (C[0][0], wq(C, .001), wq(C, .01)))
print("top 10 members by exact C (C, members in class, class id, uBA uAA uBB, z):")
for c, w, cid in ex[:10]:
    a = A[cid]; bb = B.get(cid, a['uAA'] if a['sym'] else None)
    print(f"  C {c}  w {w}  id {cid}  uBA {a['uBA']} uAA {a['uAA']} uBB {bb}  z {a['z']}")
lbmin = min(lb) if lb else None
if ex and lb:
    c10 = ex[9][0] if len(ex) >= 10 else float('inf')
    need = [x for x in lb if x[0] <= c10]
    print(f"classes with only a lower bound below the 10th best exact C ({c10}): {len(need)} (need the B-root for them)")
