"""Card c5 (squad r5-d11D5): one switch whose new line is structured.

g      = hyperbolic PG-line (9 points, pairwise non-collinear in W(8)); p_1..p_8 = 8 of its points, g9 = the 9th.
ax     = totally isotropic (W-)line disjoint from g.
q_i    = the point of ax orthogonal to p_i (unique, since p_i not on ax); L_i = span(p_i, q_i) is a W-line through p_i.
       The L_i are pairwise disjoint and all meet ax.
C      = collineation induced by a random M in GL(4,8) with C(L_i) isotropic for all switch lines and M not symplectic.
         (Such M preserve every W-line meeting ax: 73 lines, the rest are moved.)
switch : x* replaces p_i on L_i (i <= 8); new line l* = {p_1..p_8, x*}.
sigma  : old points p -> delta(C(p)) (gq.d_pt[C[p]]).
  MODE A: sigma(x*) = l*.
  MODE B: sigma(g9) = l*, sigma(x*) = delta(C(g9))  (so sigma of the points of l* are delta of the 9 points of C(g)).
KS = number of switches (second g2 is disjoint from g and from ax, same C).

usage: mkg.py seed out.in [KS=1] [A|B]
"""
import sys, random
sys.path.insert(0, "/home/user/degree-diameter/research/d11D5/dc")
from gq import *

seed, out = int(sys.argv[1]), sys.argv[2]
KS = int(sys.argv[3]) if len(sys.argv) > 3 else 1
MODE = sys.argv[4] if len(sys.argv) > 4 else "B"
rng = random.Random(seed)


def rand_hyp(avoid):
    """random hyperbolic PG-line: spanned by two points with Bf != 0; its 9 points avoid the set `avoid`"""
    while True:
        a, b = rng.sample(range(n0), 2)
        if Bf(PTS[a], PTS[b]) != 0:
            g = sorted(span(PTS[a], PTS[b]))
            if not (set(g) & avoid):
                return g


def isoimg(M, L):
    """is C(L) a W-line?  Bf of the images of two points of L (zero iff the image is totally isotropic)"""
    x, y = LINES[L][0], LINES[L][1]
    return Bf(matvec(M, PTS[x]), matvec(M, PTS[y])) == 0


def design(g):
    """8 points p_i of g, omitted point g9, L_i = span(p_i, q_i) with q_i the point of ax orthogonal to p_i"""
    om = rng.randrange(9)
    g9 = g[om]
    ps = [p for i, p in enumerate(g) if i != om]
    qs = []
    for p in ps:
        cand = [q for q in axp if Bf(PTS[p], PTS[q]) == 0]
        assert len(cand) == 1, cand
        qs.append(cand[0])
    Ls = [LIDX[span(PTS[p], PTS[q])] for p, q in zip(ps, qs)]
    return ps, Ls, g9, qs


# first hyperbolic line g and a W-line ax disjoint from it
g = rand_hyp(set())
while True:
    ax = rng.randrange(n0)
    if not (set(LINES[ax]) & set(g)):
        break
axp = LINES[ax]
sw = [design(g)]
if KS >= 2:
    # second hyperbolic line: disjoint from g and ax, its switch lines must be new and disjoint from the first ones
    for t in range(10000):
        g2 = rand_hyp(set(g) | set(axp))
        r = design(g2)
        if not (set(r[1]) & set(sw[0][1])) and r[2] not in (sw[0][2],):
            sw.append(r)
            break
    else:
        print("no second switch", file=sys.stderr)
        sys.exit(1)

# collineation C = pmap(M): every switch line maps to a W-line, and M is not symplectic
allL = [L for s in sw for L in s[1]]
tries = 0
while True:
    M = randmat(rng)
    tries += 1
    if not all(isoimg(M, L) for L in allL):
        continue
    pres = sum(isoimg(M, L) for L in range(n0))
    if pres < n0:
        break
C = pmap(M)
print(f"seed {seed} KS {KS} mode {MODE}: ax {ax} g {g} tries {tries} preserved W-lines {pres}", file=sys.stderr)

n = n0 + len(sw)
L2 = [list(l) for l in LINES]
sig = [d_pt[C[p]] for p in range(n0)]
for k, (ps, Ls, g9, qs) in enumerate(sw):
    X = n0 + k
    for L, p in zip(Ls, ps):
        L2[L] = [X if q == p else q for q in L2[L]]
    L2.append(list(ps) + [X])
    if MODE == "B":
        assert sig[g9] == d_pt[C[g9]]
        sig[g9] = n0 + k          # the old point g9 now goes to the new line l*
        sig.append(d_pt[C[g9]])   # the new point x* takes the old line delta(C(g9))
    else:
        sig.append(n0 + k)        # sigma(x*) = l*
    print(f"switch {k}: lines {Ls} points {ps} g9 {g9} q {qs}", file=sys.stderr)
assert sorted(sig) == list(range(n))
with open(out, "w") as f:
    f.write(f"{n} 9\n")
    for l in L2:
        f.write(" ".join(map(str, l)) + "\n")
    for s in sig:
        f.write(f"{s}\n")
