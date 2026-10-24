"""Duality polygon cover of W(q) (q even): base = W(q) incidence graph + matchings sigma1 = delta^-1, sigma2 = delta,
lift by Z_M with GQ voltages phi (delta-invariant), sigma voltages t1, t2.

usage: python3 dcover.py q M t1 t2 phimode seed out.txt
  phimode: zero | rand (delta-invariant values in {0, M/2}) | file:<json list of flag values>
Writes the liftcheck input and prints the count of opposite point pairs whose q+1 GQ 4-paths have one offset only.
"""
import json, sys, random

def load(q, m=None):
    W = json.load(open(f"w{q}.json"))
    n = len(W["points"]); L = W["lines"]
    if m is None:
        m = W["polarity_m"] if W["polarity_m"] is not None else 0
    fp, fl = W["frob_pt"], W["frob_ln"]
    def pw(perm, k):
        r = list(range(n))
        for _ in range(k):
            r = [perm[x] for x in r]
        return r
    fpm, flm = pw(fp, m), pw(fl, m)
    d_pt = [W["klein_pt"][fpm[x]] for x in range(n)]   # point -> line
    d_ln = [W["klein_ln"][flm[x]] for x in range(n)]   # line -> point
    inv_ln = [0] * n                                    # delta^-1 on points: point -> line
    for li in range(n):
        inv_ln[d_ln[li]] = li
    return n, L, d_pt, d_ln, inv_ln

def flags_and_orbits(n, L, d_pt, d_ln):
    fid = {}
    for li in range(n):
        for p in L[li]:
            fid[(p, li)] = len(fid)
    orb = [-1] * len(fid); norb = 0
    for (p, li), f in fid.items():
        if orb[f] >= 0:
            continue
        cur = (p, li)
        while orb[fid[cur]] < 0:
            orb[fid[cur]] = norb
            cur = (d_ln[cur[1]], d_pt[cur[0]])
        norb += 1
    return fid, orb, norb

def pt_lines(n, L):
    pl = [[] for _ in range(n)]
    for li in range(n):
        for p in L[li]:
            pl[p].append(li)
    return pl

def opposite_violations(n, L, pl, phi, fid, M):
    """count non-collinear point pairs P<Q whose q+1 paths P-L-R-M-Q all have the same offset"""
    onL = [set(s) for s in L]
    col = [set() for _ in range(n)]
    for s in L:
        for a in s:
            col[a].update(s)
    bad = 0
    for P in range(n):
        for Q in range(P + 1, n):
            if Q in col[P]:
                continue
            offs = set()
            for l1 in pl[P]:
                # R = point of l1 collinear with Q
                R = next(r for r in L[l1] if Q in col[r])
                m2 = next(m for m in pl[R] if Q in onL[m])
                o = (phi[fid[(P, l1)]] - phi[fid[(R, l1)]] + phi[fid[(R, m2)]] - phi[fid[(Q, m2)]]) % M
                offs.add(o)
                if len(offs) > 1:
                    break
            if len(offs) == 1:
                bad += 1
    return bad

if __name__ == "__main__":
    q, M, t1, t2 = map(int, sys.argv[1:5]); mode = sys.argv[5]; seed = int(sys.argv[6]); out = sys.argv[7]
    n, L, d_pt, d_ln, inv_ln = load(q)
    fid, orb, norb = flags_and_orbits(n, L, d_pt, d_ln)
    rng = random.Random(seed)
    if mode == "zero":
        ov = [0] * norb
    elif mode == "rand":
        ov = [rng.choice([0, M // 2]) for _ in range(norb)]
    elif mode.startswith("file:"):
        ob = json.load(open(mode[5:]))["orbit_bits"]
        ov = [(M // 2) * b for b in ob]
    phi = [ov[orb[f]] for f in range(len(fid))]
    pl = pt_lines(n, L)
    with open(out, "w") as fo:
        fo.write(f"{n} {n} {M}\n")
        for (p, li), f in fid.items():
            fo.write(f"{p} {li} {phi[f]}\n")
        for p in range(n):
            fo.write(f"{p} {inv_ln[p]} {t1}\n")
            fo.write(f"{p} {d_pt[p]} {t2}\n")
    print(f"q={q} M={M} t=({t1},{t2}) flags={len(fid)} delta-orbits on flags={norb}")
    print("opposite pairs with a single GQ offset:", opposite_violations(n, L, pl, phi, fid, M))
