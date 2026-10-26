"""c3: two-pair insertions into W(8) (n = 587).  Points 585 = x1, 586 = x2; lines 585 = l1, 586 = l2.
Two switches on disjoint flags of W(8) (switch 2 is applied to the base after switch 1, so it can only use flags
that switch 1 did not remove):
  nonincident k: flags (p_i, L_i) -> (x_k, L_i) and (p_i, l_k), 9 lines L_i, 9 points p_i.
  incident k:    x_k on l_{k'} (k' = k, or the cross partner), flags (p_i, L_i), i = 1..8, -> (x_k, L_i), (p_i, l_{k'}).
sigma = delta on old points; cross: sigma(x1)=l2, sigma(x2)=l1; own: sigma(x_k)=l_k.
usage: python3 gen.py VARIANT MODE SEED OUTPREFIX   (variant: a b c a2 b2 ; mode: spread random absolute ; meet=1 env)
  a  = two 9-flag switches        b = two incident switches (x_k on l_k)     c = incident, cross (x1 on l2, x2 on l1)
  a2/b2 = same with own sigma (control)
  MEET=1: lines of switch 2 must meet a line of switch 1 (variant d).  XSP=1: points/lines of switch 2 spread against switch 1."""
import sys, os, random, json
HERE = os.getcwd()
D = "/home/user/degree-diameter/research/d11D5"
os.chdir(D); sys.path.insert(0, D)
from dcover import load
N0, L0, d_pt, d_ln, inv = load(8)
L0 = [list(s) for s in L0]
col0 = [set() for _ in range(N0)]
for s in L0:
    for a in s: col0[a].update(s)
conc0 = [set(s) for s in L0]
def concurrent(a, b): return bool(conc0[a] & conc0[b])

def sample(Lsets, rng, K, mode, prev_lines, prev_pts, meet, xsp):
    """choose K old lines (< N0) and K old points, flags (p, L) present in Lsets, p not collinear with prev_pts (xsp)"""
    pl_now = None
    if mode == "absolute":
        cand = [p for p in range(N0) if p in Lsets[d_pt[p]] and not any(p in col0[q] for q in prev_pts if xsp)]
        rng.shuffle(cand)
        pts = []
        for p in cand:
            if all(p not in col0[q] for q in pts):
                pts.append(p)
                if len(pts) == K: break
        if len(pts) < K: return None
        lines = [d_pt[p] for p in pts]
        if any(l in prev_lines for l in lines) and False: return None
        return lines, pts
    lines = []
    cand = list(range(N0)); rng.shuffle(cand)
    for li in cand:
        if li in prev_lines or li in lines: continue
        if mode == "spread" and any(concurrent(li, m) for m in lines + (prev_lines if xsp else [])): continue
        if meet and not any(concurrent(li, m) for m in prev_lines): continue
        if not any(p < N0 and p in Lsets[li] for p in range(N0)) : continue
        lines.append(li)
        if len(lines) == K: break
    if len(lines) < K: return None
    pts = []
    for li in lines:
        c = [p for p in Lsets[li] if p < N0 and all(p not in col0[q] for q in pts + (prev_pts if xsp else []))]
        if not c: return None
        pts.append(rng.choice(c))
    return lines, pts

def apply(Lsets, x, l, lines, pts, incident):
    for li, p in zip(lines, pts):
        assert p in Lsets[li], (li, p)
        Lsets[li].remove(p); Lsets[li].add(x); Lsets[l].add(p)
    if incident: Lsets[l].add(x)

def build(variant, mode, rng, meet=False, xsp=False):
    Lsets = [set(s) for s in L0] + [set(), set()]
    K = 8 if variant in ("b", "b2", "c") else 9
    if variant in ("c",):
        pairs = [(585, 586), (586, 585)]   # (x_k, l_{k'})
    else:
        pairs = [(585, 585), (586, 586)]
    prev_lines, prev_pts = [], []
    allpts, alllines = [], []
    for k, (x, l) in enumerate(pairs):
        incident = variant in ("b", "b2", "c")
        s = None
        for _ in range(200):
            s = sample(Lsets, rng, K, mode, prev_lines, prev_pts, meet and k == 1, xsp and k == 1)
            if s: break
        if not s: return None
        lines, pts = s
        apply(Lsets, x, l, lines, pts, incident)
        prev_lines = prev_lines + lines; prev_pts = prev_pts + pts
    if variant in ("a2", "b2"): sig = d_pt[:] + [585, 586]
    else: sig = d_pt[:] + [586, 585]      # cross: sigma(x1) = l2, sigma(x2) = l1
    if variant == "c": sig = d_pt[:] + [586, 585]
    # validate
    deg_p = [0] * 587; deg_l = [0] * 587
    for li in range(587):
        if len(Lsets[li]) != 9: return None
        for p in Lsets[li]: deg_p[p] += 1
    if any(d != 9 for d in deg_p): return None
    if sorted(sig) != list(range(587)): return None
    return [sorted(s) for s in Lsets], sig

def write(path, Ls, sig):
    with open(path, "w") as f:
        f.write("587 9\n")
        for s in Ls: f.write(" ".join(map(str, s)) + "\n")
        for v in sig: f.write(f"{v}\n")

if __name__ == "__main__":
    variant, mode, seed, prefix = sys.argv[1], sys.argv[2], int(sys.argv[3]), sys.argv[4]
    meet = os.environ.get("MEET") == "1"; xsp = os.environ.get("XSP") == "1"
    rng = random.Random(seed)
    r = build(variant, mode, rng, meet, xsp)
    if r is None: print("FAIL"); sys.exit(0)
    p = os.path.join(HERE, prefix + ".in"); write(p, *r)
    print(p)
