"""Rigorous upper bound on N for Haar graphs of metacyclic groups whose action has small order (the 'action-order bound').

G = Z_m x|_r Z_k, (a, j)(b, l) = (a + r^j b, j + l), o = ord(r) in Z_m^* (o | k).  S = {s_0, ..., s_{Delta-1}},
s_i = (a_i, j_i), normal form s_0 = e (translate S); for prime m also a_1 = 0 (conjugate by a translation; frob_scan.py).
Universal group U = (Z[x]/(x^o - 1))^F x| Z^(Delta-1):  (P; n)(Q; n') = (P + x^(<n, j> mod o) Q; n + n'),
with generators  u_0 = e,  u_i = (eps_i or 0; e_i)  (eps_i = i-th basis vector of the F 'formal a-parts').
phi(P; n) = (sum_i P_i(r) a_i, <n, j> mod k) is a homomorphism U -> G with phi(u_i) = s_i, so every ball of the Haar
graph H(G, S) around (e, A) or (e, B) is the image of the same ball in the infinite Haar graph H(U, {u_i}).
Hence  N <= min( #A-side and #B-side vertices within D of (e,A) in H(U), same from (e,B) ),  for EVERY m and k,
given only o and the j_i mod o.  We report, for each o, the maximum of this bound over all j-patterns mod o.
'prime' mode uses F = Delta-2 formal parts (a_0 = a_1 = 0, valid for prime m); 'general' mode F = Delta-1.
Usage: python3 metabound.py DELTA D OMAX [--mode prime|general]
"""
import argparse
import itertools
from math import gcd


def ball_counts(Delta, D, o, j, F):
    """Counts of distinct A-side / B-side vertices within distance D of (e,A) and of (e,B) in H(U, {u_i})."""
    # element: (tuple of F*o ints, tuple of Delta-1 ints)
    zeroP = (0,) * (F * o)
    gens = []
    for i in range(Delta):
        P = [0] * (F * o)
        n = [0] * (Delta - 1)
        if i >= 1:
            n[i - 1] = 1
            f = i - (Delta - F)          # formal index of generator i (generators 0 .. Delta-F-1 have no a-part)
            if f >= 0:
                P[f * o + 0] = 1
        gens.append((tuple(P), tuple(n)))

    def jdot(n):
        return sum(a * b for a, b in zip(n, j)) % o

    def mul(g, h):                          # g * h
        P, n = g
        Q, m = h
        t = jdot(n)
        R = list(P)
        for f in range(F):
            for c in range(o):
                if Q[f * o + c]:
                    R[f * o + (c + t) % o] += Q[f * o + c]
        return (tuple(R), tuple(a + b for a, b in zip(n, m)))

    def inv(g):
        P, n = g
        t = (-jdot(n)) % o
        R = [0] * (F * o)
        for f in range(F):
            for c in range(o):
                if P[f * o + c]:
                    R[f * o + (c + t) % o] -= P[f * o + c]
        return (tuple(R), tuple(-a for a in n))

    ginv = [inv(g) for g in gens]
    res = []
    for start_side in ('A', 'B'):
        e = (zeroP, (0,) * (Delta - 1))
        seen = {('A' if start_side == 'A' else 'B', e)}
        frontier = [e]
        side = start_side
        cnt = {'A': 0, 'B': 0}
        cnt[side] += 1
        for d in range(1, D + 1):
            nxt = []
            nside = 'B' if side == 'A' else 'A'
            for g in frontier:
                for i in range(Delta):
                    # (g,A) ~ (s g, B); (g,B) ~ (s^-1 g, A)
                    h = mul(gens[i], g) if side == 'A' else mul(ginv[i], g)
                    key = (nside, h)
                    if key not in seen:
                        seen.add(key)
                        nxt.append(h)
            cnt[nside] += len(nxt)
            frontier, side = nxt, nside
        res.append((cnt['A'], cnt['B']))
    return min(res[0][0], res[0][1], res[1][0], res[1][1]), res


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('Delta', type=int)
    ap.add_argument('D', type=int)
    ap.add_argument('omax', type=int)
    ap.add_argument('--omin', type=int, default=1)
    ap.add_argument('--mode', default='prime', choices=['prime', 'general'])
    a = ap.parse_args()
    F = a.Delta - 2 if a.mode == 'prime' else a.Delta - 1
    print(f'# Delta={a.Delta} D={a.D} mode={a.mode} (F={F} formal a-parts): max over j mod o of the ball bound')
    print('# o  bound  best_j  (A,B from (e,A); A,B from (e,B))')
    for o in range(a.omin, a.omax + 1):
        best, bj, bres = -1, None, None
        seen_classes = set()
        for j in itertools.product(range(o), repeat=a.Delta - 1):
            # j -> u*j (u a unit mod o) gives an isomorphic universal group (x -> x^u): skip repeats
            cls = min(tuple((u * x) % o for x in j) for u in range(1, o + 1) if gcd(u, o) == 1) if o > 1 else j
            if cls in seen_classes:
                continue
            seen_classes.add(cls)
            b, res = ball_counts(a.Delta, a.D, o, j, F)
            if b > best:
                best, bj, bres = b, j, res
        print(f'{o:3d}  {best:7d}  j={bj}  {bres}', flush=True)


if __name__ == '__main__':
    main()
