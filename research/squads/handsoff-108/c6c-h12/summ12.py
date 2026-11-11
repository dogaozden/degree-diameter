# summ12.py FAMILY: summary of out/FAMILY_scanA.tsv (A-root part per class, from exh12 scanA) and out/FAMILY_scanB.tsv.
# FAMILY in {A4, D6nsq, D6sq}. Members = double-coset sets (degree 10); a class with orbit weight w stands for w sets.
# Exact full C = uBA+uAA+uBB when the B line exists or the class is self-inverse (uBB = uAA, C = uBA + 2 uAA);
# otherwise only the lower bound P = uBA+uAA is known. Units: h = 12, so per-unit values are plain / 12.
import sys, os
fam = sys.argv[1]
base = os.path.dirname(os.path.abspath(__file__)) + '/out/'
TOTAL = {'A4': 13797, 'D6nsq': 27408, 'D6sq': 40480}[fam]
H = 12
A = {}
for line in open(base + fam + '_scanA.tsv'):
    t = line.split()
    if len(t) < 7 or t[0] != 'A': continue
    A[t[1]] = dict(orb=int(t[2]), sym=int(t[3]), uBA=int(t[4]), uAA=int(t[5]), part=t[6])
B = {}
if os.path.exists(base + fam + '_scanB.tsv'):
    for line in open(base + fam + '_scanB.tsv'):
        t = line.split()
        if len(t) >= 3 and t[0] == 'B': B[t[1]] = int(t[2])
nmem = sum(a['orb'] for a in A.values())
print(f"{fam}: classes {len(A)}, members covered {nmem} of {TOTAL} ({'complete' if nmem == TOTAL else 'PARTIAL'}), B-root known for {len(B)} classes")
def wq(vals, q):
    tot = sum(w for _, w in vals); acc = 0
    for v, w in sorted(vals):
        acc += w
        if acc >= q * tot: return v
    return vals[-1][0]
P = [(a['uBA'] + a['uAA'], a['orb']) for a in A.values()]
print("lower bound P = uBA+uAA over members: min %d p0.1 %d p1 %d median %d (median per unit of h: %.1f)" % (
    min(p for p, _ in P), wq(P, .001), wq(P, .01), wq(P, .5), wq(P, .5) / H))
ex = []; lb = []
for k, a in A.items():
    if a['sym']: ex.append((a['uBA'] + 2 * a['uAA'], a['orb'], k))
    elif k in B: ex.append((a['uBA'] + a['uAA'] + B[k], a['orb'], k))
    else: lb.append((a['uBA'] + a['uAA'], a['orb'], k))
nex = sum(w for _, w, _ in ex)
print(f"exact full C known for {len(ex)} classes = {nex} members (self-inverse classes: {sum(1 for a in A.values() if a['sym'])})")
if ex:
    C = [(c, w) for c, w, _ in ex]
    print("exact C over known members: min %d p0.1 %d p1 %d median %d" % (min(C)[0], wq(C, .001), wq(C, .01), wq(C, .5)))
ex.sort()
print("top 10 exact C (C, members, class key, uBA uAA uBB, partition):")
for c, w, k in ex[:10]:
    a = A[k]; bb = B.get(k, a['uAA'] if a['sym'] else None)
    print(f"  C {c}  w {w}  key {k}  uBA {a['uBA']} uAA {a['uAA']} uBB {bb}  {a['part']}")
lb.sort()
print("lowest lower bounds of classes without exact C (P, members, key, partition):")
for p, w, k in lb[:5]:
    print(f"  P {p}  w {w}  key {k}  {A[k]['part']}")
print("per partition (members, median P, min P) over scanned classes:")
parts = sorted(set(a['part'] for a in A.values()))
for pt in parts:
    vals = [(a['uBA'] + a['uAA'], a['orb']) for a in A.values() if a['part'] == pt]
    mem = sum(w for _, w in vals)
    print(f"  {pt:14s} members {mem:6d} min P {min(v for v,_ in vals):7d} median P {wq(vals, .5):7d} (per unit {wq(vals, .5)/H:6.1f})")
