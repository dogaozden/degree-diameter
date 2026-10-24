#!/usr/bin/env python3
"""Card d8 (round r2-d8): Z_3 polygon cover x Z_k lifts of H(q) plus ONE hop matching, k = (q-1)/2.

Base graph: incidence graph of H(q) (points 0..N-1, lines N..2N-1) plus a hop bijection s: points -> lines
(so every vertex has degree q+2). Group Z_3 x Z_k (liftdiam M1 = 3, M2 = k).
  hop  p -> s(p)   voltage (1, w(p))      (Z_3 polygon part is 1 on the hop, as in the card)
  flag p -> L      voltage (0, c(p, L))   (Z_k part from GF(q)*/{+-1})

Flag modes
  zero  : c = 0
  frame : rule on L = the two smallest point ids a, b on L. Write v_p = alpha*v_a + beta*v_b (projective
          coordinates of H(q) in PG(6,q)); lambda = beta/alpha in GF(q)*; c = dlog(lambda) mod k
          (dlog w.r.t. the smallest primitive root; mod k identifies lambda with -lambda, i.e. GF(q)*/{+-1}).
          c = 0 for p in {a, b} (lambda = 0 or infinity).
  rand  : c uniform in Z_k (seeded)

Hop modes
  rand  : w uniform in Z_k (seeded)
  zero  : w = 0
  coord : w(p) = dlog(P[p][j]) mod k with j the last nonzero coordinate of p (GF(q)*/{+-1} class)

Usage: python3 -I d8lift.py q flags hop seed [--step S] [--D 8]
Prints one JSON line with unreached_pairs from liftdiam (sampling every S-th base source).
"""
import argparse
import collections
import json
import os
import random
import subprocess
import sys

GH_DIR = '/home/user/degree-diameter/research/theorems/d8'
sys.path.insert(0, GH_DIR)
import gh  # noqa: E402

LIFTDIAM = os.path.join(GH_DIR, 'liftdiam')
SCR = '/tmp/claude-0/-home-user-degree-diameter/0ad899b8-ae47-58b5-b704-0795802a53c1/scratchpad/d8'


def dlog_table(q):
    """element -> exponent for the nonzero elements of GF(q) (q prime) w.r.t. the smallest primitive root."""
    for g in range(2, q):
        seen, x = {}, 1
        for i in range(q - 1):
            seen[x] = i
            x = x * g % q
        if len(seen) == q - 1:
            return seen
    raise ValueError(q)


def frame_flag_labels(H, q, k, ell):
    N = H.N
    P = [[int(c) for c in row] for row in H.P]
    lab = {}
    for L in range(N):
        pts = [int(x) for x in H.lines[L]]
        a, b = pts[0], pts[1]
        va, vb = P[a], P[b]
        pair = None
        for i1 in range(7):
            for i2 in range(i1 + 1, 7):
                det = (va[i1] * vb[i2] - va[i2] * vb[i1]) % q
                if det:
                    pair = (i1, i2, det)
                    break
            if pair:
                break
        assert pair is not None
        i1, i2, det = pair
        idet = pow(det, q - 2, q)
        for p in pts:
            vp = P[p]
            al = (vp[i1] * vb[i2] - vp[i2] * vb[i1]) * idet % q
            be = (va[i1] * vp[i2] - va[i2] * vp[i1]) * idet % q
            assert all((al * va[t] + be * vb[t] - vp[t]) % q == 0 for t in range(7)), (p, L)
            if al == 0 or be == 0:
                c = 0
            else:
                c = ell[be * pow(al, q - 2, q) % q] % k
            lab[(p, N + L)] = c
    return lab


def coboundary_violations(lab, k):
    """0 iff the flag labelling is switching-equivalent to zero (c(p,L) = phi(L) - phi(p) for some phi)."""
    adj = collections.defaultdict(list)
    for (p, Lv), c in lab.items():
        adj[p].append((Lv, c % k))
        adj[Lv].append((p, (-c) % k))
    pot = {}
    for s in adj:
        if s in pot:
            continue
        pot[s] = 0
        stack = [s]
        while stack:
            u = stack.pop()
            for v, c in adj[u]:
                if v not in pot:
                    pot[v] = (pot[u] + c) % k
                    stack.append(v)
    return sum(1 for (p, Lv), c in lab.items() if (pot[Lv] - pot[p]) % k != c % k)


def hop_labels(H, q, k, ell, kind, rng):
    out = []
    for p in range(H.N):
        if kind == 'rand':
            out.append(rng.randrange(k))
        elif kind == 'zero':
            out.append(0)
        else:
            row = [int(c) for c in H.P[p]]
            last = max(i for i in range(7) if row[i] % q)
            out.append(ell[row[last]] % k)
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('q', type=int)
    ap.add_argument('flags', choices=['zero', 'frame', 'rand'])
    ap.add_argument('hop', choices=['rand', 'zero', 'coord'])
    ap.add_argument('seed', type=int)
    ap.add_argument('--step', type=int, default=13)
    ap.add_argument('--D', type=int, default=8)
    args = ap.parse_args()

    q = args.q
    k = (q - 1) // 2
    M1 = 3
    H = gh.load(q)
    N = H.N
    ell = dlog_table(q)
    rng = random.Random(args.seed)

    if args.flags == 'zero':
        flag = {(p, Lv): 0 for (p, Lv) in gh.flags(H)}
    elif args.flags == 'frame':
        flag = frame_flag_labels(H, q, k, ell)
    else:
        flag = {(p, Lv): rng.randrange(k) for (p, Lv) in gh.flags(H)}
    viol = coboundary_violations(flag, k)

    w = hop_labels(H, q, k, ell, args.hop, rng)
    s = list(range(N))
    rng.shuffle(s)

    edges = [(p, Lv, 0, flag[(p, Lv)]) for (p, Lv) in gh.flags(H)]
    edges += [(p, N + s[p], 1, w[p]) for p in range(N)]

    tag = f'q{q}_{args.flags}_{args.hop}_s{args.seed}'
    path = os.path.join(SCR, f'base_{tag}.txt')
    gh.write_base(path, 2 * N, M1, k, edges)
    out = subprocess.run([LIFTDIAM, path, str(args.D), '1', str(args.step)],
                         capture_output=True, text=True).stdout
    unr = int(out.split('unreached_pairs')[1].split()[0])
    ecc = out.split('max_ecc')[1].split()[0]
    lab_hist = collections.Counter(flag.values())
    res = {
        'tag': tag, 'q': q, 'M': M1 * k, 'group': f'Z{M1}xZ{k}', 'flags': args.flags, 'hop': args.hop,
        'seed': args.seed, 'step': args.step, 'D': args.D, 'unreached_pairs': unr, 'max_ecc': ecc,
        'flag_coboundary_violations': viol, 'flag_label_hist': dict(sorted(lab_hist.items())),
        'base': path,
    }
    print(json.dumps(res), flush=True)
    print(out.strip(), flush=True)


if __name__ == '__main__':
    main()
