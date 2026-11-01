#!/usr/bin/env python3
"""c13 model: predicted number of independent hole CLUMPS for odd-D (D = 11) Haar graphs H(G,S),
G = SL(2,p) x Z_n or PSL(2,p) x Z_n, ORBIT "3 m f" (alpha = conj by g of order 3, times z -> r z).
usage: model.py clumps d group...   |  model.py validate  |  model.py pick d lo hi  (ranks pick11 candidates)
P(cost 0) ~ exp(-K) with K = clumps (both sides, central counted once) + empirical n^2 penalty (see MODEL.md).
"""
import math, sys, subprocess
D = 11
REC = {7: 11012976, 8: 45329808, 9: 155250816, 10: 460691568, 11: 1241299248, 12: 2976066240,
       13: 6781213392, 14: 14381398080}
H = 5  # odd D = 2h+1, h = 5 at D = 11
KAPPA = {"sl": 0.007, "psl": 0.004}  # measured extra cost per n^2 (RANDORB medians, Delta 7), see MODEL.md

def W(d, D=D):
    return 1 + sum(d * (d - 1) ** (2 * i - 1) for i in range(1, (D - 1) // 2 + 1))

def alpha_orbits_Zn(n):
    """number of orbits of z -> r z on Z_n, r a cube root of 1 mod n (r != 1) with fewest fixed points."""
    if n == 1:
        return 1, None
    best = None
    for r in range(2, n):
        if pow(r, 3, n) == 1 and r != 1:
            fixed = sum(1 for z in range(n) if (r * z - z) % n == 0)
            if best is None or fixed < best[0]:
                best = (fixed, r)
    if best is None:
        return None, None
    r = best[1]
    seen = [False] * n; orb = 0
    for z in range(n):
        if not seen[z]:
            orb += 1; y = z
            while not seen[y]:
                seen[y] = True; y = (r * y) % n
    return orb, r

def group_feats(d, fam, p, n):
    base = p * (p * p - 1) if fam == "sl" else p * (p * p - 1) // 2
    N = base * n
    lam = W(d) / N
    mu = N * math.exp(-lam)
    if fam == "sl":
        I = 1                                  # only -I (n odd)
        C = 2 * n                              # (+-I, z)
        Fix = (p - 1) if p % 3 == 1 else (p + 1)  # centralizer of alpha in SL(2,p), z = 0
        orbZ, _ = alpha_orbits_Zn(n)
        cen_orb = 2 * orbZ - 1                 # central alpha-orbits, minus identity
    else:
        eps = 1 if p % 4 == 1 else -1
        I = p * (p + eps) // 2                 # involutions of PSL(2,p), z = 0 (n odd)
        C = n
        Fix = (p - 1 if p % 3 == 1 else p + 1) // 2
        orbZ, _ = alpha_orbits_Zn(n)
        cen_orb = orbZ - 1
    clumps_side = mu / 6 + I * math.exp(-lam / 2) / 3 + Fix * math.exp(-lam / 3) / 2
    clumps_cen = cen_orb * math.exp(-lam / H)  # central holes are holes on both sides: counted once
    K_clump = 2 * clumps_side + clumps_cen
    K_pen = KAPPA[fam] * n * n / 6.0           # empirical large-n penalty, cost -> clumps (cost ~ 6 per clump)
    return dict(N=N, lam=lam, mu=mu, I=I, C=C, F=Fix, cen_orb=cen_orb, K_clump=K_clump,
                K_pen=K_pen, K=K_clump + K_pen, cost_pred=2 * 1.7 * mu + 2 * 1.3 * I * math.exp(-lam / 2)
                + 2 * 2.2 * C * math.exp(-lam / H) / 2 + KAPPA[fam] * n * n)

def pick(d, lo, hi):
    out = subprocess.run(["python3", "/home/user/degree-diameter/research/squads/raise11/bin/pick11.py",
                          str(d), str(lo), str(hi), "all", "2000"], capture_output=True, text=True).stdout
    rows = []
    for line in out.splitlines():
        parts = line.split()
        fam = parts[0]; p = int(parts[1]); n = int(parts[2])
        if fam not in ("sl", "psl"):
            continue
        f = group_feats(d, fam, p, n)
        gain = 100 * (f["N"] / (REC[d] // 2) - 1)
        rows.append((f["K"], fam, p, n, gain, f))
    rows.sort()
    return rows

if __name__ == "__main__":
    cmd = sys.argv[1]
    if cmd == "pick":
        d = int(sys.argv[2]); lo = float(sys.argv[3]); hi = float(sys.argv[4])
        for K, fam, p, n, gain, f in pick(d, lo, hi)[:5]:
            print(f"d={d} {fam} {p} {n} gain={gain:.2f}% N={f['N']} mu={f['mu']:.2f} K={K:.3f} "
                  f"Kclump={f['K_clump']:.3f} Kpen={f['K_pen']:.3f}")
    elif cmd == "clumps":
        d = int(sys.argv[2])
        for spec in sys.argv[3:]:
            fam, p, n = spec.split(":"); f = group_feats(d, fam, int(p), int(n))
            print(spec, {k: (round(v, 4) if isinstance(v, float) else v) for k, v in f.items()})
