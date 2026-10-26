"""Build an H-equivariant DM base: W(8) + k new pairs as one H-orbit of switches.
H is given as a list of group elements on the 585 old points / lines (perm arrays), with the
identity first.  Group element j acts on new pair index i by mult[j][i] (left multiplication).
Writes the plusopt format (n dg; n lines of points; n sigma values) and a group file for the annealer:
  "m" then for each element: a line of n point images and a line of n line images (n = 585 + k).
usage: python3 mkorb.py group in.json mode seed out.in out.grp   (group: 'frob' or 'frob' only for now;
   mode: plus9 | inc8 | plus9spread | inc8spread)"""
import sys, os, random, json
CWD = os.getcwd()
sys.path.insert(0, "/home/user/degree-diameter/research/d11D5")
os.chdir("/home/user/degree-diameter/research/d11D5")
from dcover import load
gname, mode, seed, out, outg = sys.argv[1], sys.argv[2], int(sys.argv[3]), os.path.join(CWD, sys.argv[4]), os.path.join(CWD, sys.argv[5])
rng = random.Random(seed)
n0, L0, d_pt, d_ln, inv = load(8)
W = json.load(open("w8.json"))
fp, fl = W["frob_pt"], W["frob_ln"]
# group elements (old vertices): identity and powers of frob
if gname == "frob":
    gens = [(fp, fl)]
else:
    gj = json.load(open(gname))
    gens = [(gj["pt"][:n0], gj["ln"][:n0])]
elems = [(list(range(n0)), list(range(n0)))]
def comp(a, b):  # a after b
    return [a[x] for x in b]
while True:
    last = elems[-1]
    nxt = (comp(gens[0][0], last[0]), comp(gens[0][1], last[1]))
    if nxt == elems[0]: break
    elems.append(nxt)
k = len(elems)
mult = [[0] * k for _ in range(k)]
for a in range(k):
    for b in range(k):
        # element a * element b  (as composition of perms: apply b then a)
        pa, la = elems[a]; pb, lb = elems[b]
        pp = comp(pa, pb); ll = comp(la, lb)
        mult[a][b] = next(c for c in range(k) if elems[c][0] == pp and elems[c][1] == ll)
n = n0 + k
L = [list(s) for s in L0]
pts_of_line = L
col = [set() for _ in range(n0)]
for s in L:
    for a in s: col[a].update(s)
pl = [[] for _ in range(n0)]
for li, s in enumerate(L):
    for p in s: pl[p].append(li)
m = 9 if mode.startswith("plus9") else 8
spread = mode.endswith("spread")
def orbit_flag(p, l):  # list of flags (g p, g l) for all g
    return [(elems[g][0][p], elems[g][1][l]) for g in range(k)]
def flag_stab_free(p, l):
    return len(set(orbit_flag(p, l))) == k
def try_switch():
    # choose m flags (p_i, L_i): distinct lines, distinct points, one per H-orbit of flags, free orbits
    used_orb = set(); chosen = []; lines_used = set(); pts_used = set()
    cand = [(p, l) for l in range(n0) for p in L[l]]
    rng.shuffle(cand)
    for (p, l) in cand:
        if len(chosen) == m: break
        if l in lines_used or p in pts_used: continue
        orb = orbit_flag(p, l)
        if len(set(orb)) != k: continue
        key = min(orb)
        if key in used_orb: continue
        if spread and any(q in col[p] for (q, _) in chosen): continue
        chosen.append((p, l)); used_orb.update(orb); lines_used.add(l); pts_used.add(p)
    return chosen if len(chosen) == m else None
def build():
    for _ in range(100000):
        ch = try_switch()
        if ch: return ch
    raise SystemExit("no switch")
ch = build()
# new structure: new pair j = element j applied to the base pair (x*, l*)
NEW = list(range(n0, n))          # new point ids n0+j, new line ids n0+j
Lnew = [s[:] for s in L] + [[] for _ in range(k)]
for li in range(n0): pass
# old lines lose p_i, gain x_j*; x_j* is on g_j(L_i) for all i
for g in range(k):
    for (p, l) in ch:
        pg, lg = elems[g][0][p], elems[g][1][l]
        Lnew[lg].remove(pg)
        Lnew[lg].append(n0 + g)
    # x_g* gets lines g(L_i) ; l_g* gets points g(p_i)
    if mode.startswith("inc8"):
        pass
for g in range(k):
    if mode.startswith("plus9"):
        Lnew[n0 + g] = [elems[g][0][p] for (p, l) in ch]
        # note: plus9 new line l_g* through g(p_i): its points
    else:
        Lnew[n0 + g] = [elems[g][0][p] for (p, l) in ch] + [n0 + g]
# inc8 : x*~l* flag; x_g* lies on l_g*: add x_g* to l_g* (x* is new point n0+g) -> Lnew[n0+g] already includes n0+g
# the point x_g* needs its lines: g(L_i) (done above) plus, for inc8, the line l_g* (its own new line)
if mode.startswith("inc8"):
    for g in range(k):
        Lnew[n0 + g] = [elems[g][0][p] for (p, l) in ch] + [n0 + g]
# NOTE: new point ids are n0+g and new line ids are n0+g; line n0+g is l_g*, its points include point n0+g
for li in range(n):
    if len(Lnew[li]) != 9:
        raise SystemExit(f"degree {len(Lnew[li])} at line {li}")
# sigma
sigma = d_pt[:] + [n0 + g for g in range(k)]
sigma = [0] * n
for p in range(n0): sigma[p] = d_pt[p]
for g in range(k): sigma[n0 + g] = n0 + g
# check: points degree and simple
pdeg = [0] * n
for li in range(n):
    for p in Lnew[li]: pdeg[p] += 1
assert set(pdeg) == {9}, set(pdeg)
assert all(len(set(s)) == 9 for s in Lnew)
# group on full vertex set
gp = []; gl = []
for g in range(k):
    gp.append(elems[g][0] + [n0 + mult[g][i] for i in range(k)])
    gl.append(elems[g][1] + [n0 + mult[g][i] for i in range(k)])
# invariance checks
for g in range(k):
    for li in range(n):
        assert sorted(gp[g][p] for p in Lnew[li]) == sorted(Lnew[gl[g][li]]), ("not invariant", g, li)
    for p in range(n):
        assert gl[g][sigma[p]] == sigma[gp[g][p]], ("sigma not equivariant", g, p)
with open(out, "w") as f:
    f.write(f"{n} 9\n")
    for s in Lnew: f.write(" ".join(map(str, s)) + "\n")
    for v in sigma: f.write(f"{v}\n")
with open(outg, "w") as f:
    f.write(f"{k}\n")
    for g in range(k):
        f.write(" ".join(map(str, gp[g])) + "\n" + " ".join(map(str, gl[g])) + "\n")
print("k", k, "n", n, "switch", ch, "->", out)
