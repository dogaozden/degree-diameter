#!/usr/bin/env python3
"""classes68.py: how many inequivalent solutions are there, and how big is each one's class?  (ORDER2.md 3.4)

If S is a beta-invariant generating set, so are h S h' for h, h' in Fix(beta), and phi(S) for automorphisms phi that
commute with beta; all give isomorphic Haar graphs (relabel one side).  So valid symmetric S come in whole classes, and
if any solution exists then
    P(random symmetric S is valid) >= (class size) / (number of symmetric S).
This script, for each solution file:
  - recovers the beta-invariant frame (the files are normalised to s_0 = e by a right translation);
  - counts the stabiliser of S in Fix(beta) x Fix(beta) acting by S -> h S h'  (class size = |Fix|^2 / stabiliser,
    before automorphisms and S -> S^-1);
  - prints a class invariant: the sorted traces of s_i^-1 s_j and of s_i s_j^-1 (i != j), each multiset reduced
    modulo the field automorphisms (and sign, for PSL).  Different invariants = different classes.
Usage: classes68.py sl 25 --frob 1 FILE...      classes68.py sl 25 --alpha "mat(5,21,12,20)" FILE...
       classes68.py psl 11 24 --alpha "mat(5,1,7,6)" --r 11 FILE...
"""
import argparse, math
import numpy as np
from hgroups import read_solution
from twist import alpha_perm, find_conj


def frame(G, S, beta):
    Sarr = np.array(S)
    for t in [G.ident] + list(range(G.N)):
        T = G.mul_vec(Sarr, np.full(len(S), t))
        if set(beta[T].tolist()) == set(T.tolist()):
            return [int(x) for x in T]
    return None


def trace_invariant(G, S):
    """sorted trace multisets of s_i^-1 s_j and s_i s_j^-1 (Q part), modulo Frobenius (and sign for PSL)."""
    Q, n = G.Q, G.n
    F = Q.F
    S = np.array(S)
    inv = G.inv_perm()
    out = []
    for kind in (0, 1):
        tr = []
        for i in range(len(S)):
            for j in range(len(S)):
                if i == j:
                    continue
                x = G.mul_vec(np.array([inv[S[i]]]), np.array([S[j]]))[0] if kind == 0 else \
                    G.mul_vec(np.array([S[i]]), np.array([inv[S[j]]]))[0]
                t = int(Q.trace(np.array([x // n]))[0])
                if Q.kind == "psl":                # PSL: the trace is defined up to sign
                    t = min(t, int(F.neg[t]))
                tr.append((t, int(x % n)))
        out.append(tr)
    # reduce modulo field automorphisms t -> t^(p^j) and units u of Z_n (z -> u z): least image wins
    p, k = F.p, F.k
    def frob(t, j):
        y = 1
        for _ in range(p ** j):
            y = int(F.mul[y, t])
        return y if t else 0
    units = [u for u in range(1, n + 1) if math.gcd(u, n) == 1] if n > 1 else [1]
    best = None
    for j in range(k):
        for u in units:
            img = []
            for tr in out:
                m = []
                for t, z in tr:
                    w = frob(t, j)
                    if Q.kind == "psl":
                        w = min(w, int(F.neg[w]))
                    m.append((w, (u * z) % n))
                img.append(tuple(sorted(m)))
            img = tuple(sorted(img))          # S -> S^-1 swaps the two multisets
            if best is None or img < best:
                best = img
    return best


def stabiliser(G, S, fixset):
    """number of (h, h') in fixset^2 with h S h' = S (as sets)."""
    Sset = set(S)
    S = np.array(S)
    cnt = 0
    for h in fixset:
        hS = G.mul_vec(np.full(len(S), h), S)
        for h2 in fixset:
            T = G.mul_vec(hS, np.full(len(S), h2))
            if set(T.tolist()) == Sset:
                cnt += 1
    return cnt


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("group", nargs="+")
    ap.add_argument("--alpha", default=None)
    ap.add_argument("--frob", type=int, default=None)
    ap.add_argument("--r", type=int, default=1)
    ap.add_argument("--files", nargs="+", required=True)
    A = ap.parse_args()
    invs = {}
    for path in A.files:
        d, D, G, S = read_solution(path)
        beta = alpha_perm(G, frob=A.frob, r=A.r) if A.frob is not None else alpha_perm(G, conj=find_conj(G.Q, A.alpha), r=A.r)
        fixset = np.where(beta == np.arange(G.N))[0]
        Sy = frame(G, S, beta)
        st = stabiliser(G, Sy, fixset) if Sy is not None else -1
        inv = trace_invariant(G, S)
        key = hash(inv)
        invs.setdefault(key, []).append(path.split("/")[-1])
        print(f"{path.split('/')[-1]:34s} |Fix|={len(fixset):4d} frame={'yes' if Sy else 'NO '} "
              f"stab(hSh')={st:3d} class>={len(fixset)**2 // max(st, 1):6d}  invariant={key & 0xffffffff:08x}")
    print(f"{len(invs)} distinct invariants among {len(A.files)} solutions")
    for k, v in invs.items():
        print(f"  {k & 0xffffffff:08x}: {' '.join(v)}")


if __name__ == "__main__":
    main()
