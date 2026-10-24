#!/usr/bin/env python3
"""targets.py: which elements stay uncovered, by type, for random beta-invariant S (ORDER2.md section 3).

For every sample S (random beta-invariant with m orbits of size 2 and f fixed generators, e included when f >= 1),
the uncovered elements of each binding side are split into
  Fix   = Fix(beta)                         (beta(x) = x)
  Anti  = Anti(beta) minus Fix              (beta(x) = x^-1)
  Inv   = involutions of G minus Fix, Anti  (x = x^-1)
  other = everything else
and the miss rate of each class (uncovered / class size, summed over sides and samples) is printed.

Parameter-free prediction (clumped Poisson): if the words hitting x come in groups of |Stab(x)| (Stab in the
symmetry group of the binding word multiset), x is missed with probability ~ exp(-lambda/|Stab(x)|).  So with
p = miss rate of 'other' (Stab = 1):
  even D (word set invariant under beta only):     Fix ~ sqrt(p), Anti ~ p, Inv ~ p
  odd D  (each side invariant under beta and x->x^-1, hence under beta* = inv o beta):
                                                   Fix ~ sqrt(p), Anti ~ sqrt(p), Inv ~ sqrt(p)
Usage: targets.py GROUP... N_CYC --d D_ --D D --m M --f F [--alpha mat(..) | --frob J] [--r R] [--samples K]
       [--random]   (random S instead of beta-invariant S; beta is then only used to classify)
"""
import argparse, json, math, sys, time
import numpy as np
from hgroups import Group, parse_group
from twist import Haar, alpha_perm, find_conj, random_symmetric_S


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("group", nargs="+")
    ap.add_argument("--d", type=int, required=True)
    ap.add_argument("--D", type=int, required=True)
    ap.add_argument("--m", type=int, default=0)
    ap.add_argument("--f", type=int, default=0)
    ap.add_argument("--alpha", default=None)
    ap.add_argument("--frob", type=int, default=None)
    ap.add_argument("--r", type=int, default=1)
    ap.add_argument("--samples", type=int, default=200)
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument("--random", action="store_true")
    ap.add_argument("--json", default=None)
    A = ap.parse_args()
    Q, rest = parse_group(A.group)
    n = int(rest[0]) if rest else 1
    G = Group(Q, n)
    N = G.N
    if A.frob is not None:
        beta = alpha_perm(G, frob=A.frob, r=A.r)
    else:
        if A.alpha is None:
            tr = Q.trace(np.arange(Q.order))
            conj = int(np.nonzero(tr == 0)[0][0])
        else:
            conj = find_conj(Q, A.alpha)
        beta = alpha_perm(G, conj=conj, r=A.r)
    assert np.all(beta[beta] == np.arange(N))
    inv = G.inv_perm()
    ar = np.arange(N)
    isfix = beta == ar
    isanti = (beta == inv) & ~isfix
    isinv = (inv == ar) & ~isfix & ~isanti
    other = ~(isfix | isanti | isinv)
    sizes = dict(Fix=int(isfix.sum()), Anti=int(isanti.sum()), Inv=int(isinv.sum()), other=int(other.sum()))
    fixed_pool = np.nonzero(isfix)[0]
    fixed_pool = fixed_pool[fixed_pool != G.ident]
    rng = np.random.default_rng(A.seed)
    miss = dict(Fix=0, Anti=0, Inv=0, other=0)
    tot = dict(Fix=0, Anti=0, Inv=0, other=0)
    costs = []
    per = []                  # per sample: misses per class (summed over sides)
    t0 = time.time()
    used = 0
    for t in range(A.samples):
        if A.random:
            S = [G.ident]
            while len(S) < A.d:
                x = int(rng.integers(N))
                if x not in S:
                    S.append(x)
        else:
            S = random_symmetric_S(G, beta, A.m, A.f, rng, fixed_pool)
        H = Haar(G, S)
        c, _, V = H.cost(A.D)
        if c >= N / 2:          # not generating
            continue
        used += 1
        costs.append(c)
        if A.D % 2 == 0:
            unc = [~V[1]]
        else:
            VA, VB = V
            unc = [~VA[0], ~VB[1]]
        row = dict(Fix=0, Anti=0, Inv=0, other=0)
        for U in unc:
            for name, cls in (("Fix", isfix), ("Anti", isanti), ("Inv", isinv), ("other", other)):
                k = int((U & cls).sum())
                miss[name] += k; row[name] += k
                tot[name] += int(cls.sum())
        per.append(row)
    rate = {k: (miss[k] / tot[k] if tot[k] else float("nan")) for k in miss}
    p = rate["other"]
    pred_sqrt = math.sqrt(p) if p > 0 else float("nan")
    res = dict(group=G.spec, N=N, d=A.d, D=A.D, m=A.m, f=A.f, random=A.random, frob=A.frob, r=A.r,
               class_sizes=sizes, samples_used=used, median_cost=float(np.median(costs)) if costs else None,
               miss_rate=rate, sqrt_other=pred_sqrt,
               ratio_to_other={k: (rate[k] / p if p > 0 else None) for k in rate},
               ratio_to_sqrt_other={k: (rate[k] / pred_sqrt if p > 0 else None) for k in rate},
               seconds=round(time.time() - t0, 1))
    # binned by the sample's own generic miss rate (avoids mixing good and bad S): pooled class rates per bin
    sides = 1 if A.D % 2 == 0 else 2
    po = np.array([r["other"] for r in per], float) / (sides * max(sizes["other"], 1))
    order = np.argsort(po)
    bins = []
    nb = 4 if len(per) >= 40 else 2
    for b in range(nb):
        idx = order[b * len(order) // nb:(b + 1) * len(order) // nb]
        if len(idx) == 0:
            continue
        rr = {}
        for name in ("Fix", "Anti", "Inv", "other"):
            denom = sides * sizes[name] * len(idx)
            rr[name] = sum(per[i][name] for i in idx) / denom if denom else float("nan")
        pb = rr["other"]
        bins.append(dict(samples=len(idx), other=pb, sqrt_other=math.sqrt(pb) if pb > 0 else None,
                         Fix=rr["Fix"], Anti=rr["Anti"], Inv=rr["Inv"],
                         Anti_over_other=(rr["Anti"] / pb if pb > 0 else None),
                         Anti_over_sqrt_other=(rr["Anti"] / math.sqrt(pb) if pb > 0 else None),
                         Fix_over_sqrt_other=(rr["Fix"] / math.sqrt(pb) if pb > 0 else None)))
    res["bins_by_generic_rate"] = bins
    print(json.dumps(res, indent=1))
    if A.json:
        json.dump(res, open(A.json, "w"), indent=1)


if __name__ == "__main__":
    main()
