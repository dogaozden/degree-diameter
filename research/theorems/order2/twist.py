#!/usr/bin/env python3
"""twist.py: coverage and word-coincidence census of a Haar graph H(G,S) with S invariant under an involutive
automorphism beta of G (orbits of size 2), as in haar_sym's ORBIT="2 m f".

Convention (haar_gen3): edges (g,A) ~ (s g, B).  A walk from (e,A) with letters i_1, i_2, ... has value
... s_{i_3} s_{i_2}^-1 s_{i_1}; the binding condition at even D is that the reduced alternating words of length <= D-1
cover G on side B, at odd D that those of length <= D-1 cover G on side A from (e,A) and on side B from (e,B).

Census (ORDER2.md section 2).  beta* = inversion o beta is an anti-automorphism; Anti(beta) = Fix(beta*) =
{u : beta(u) = u^-1}.  For an even alternating word v (a contiguous subword of a binding word), its reflection
v' = sigma(reverse-and-flip(v)) is a word of the same length and sign pattern with value beta(v)^-1, so v and v'
coincide iff v lies in Anti.  Each such coincidence closes a "twisted cycle" v.sigma(v) of length 2|v| in the graph.
Counted: for each even length 2j, the number of reduced alternating words v of length 2j (both sign patterns) with
v in Anti and v' != v as words (sigma-palindromes excluded).  A twisted relator of length 4j accounts for 8j such
half-words, so  twisted relators of length 4j  ~=  count / 8j.
Also counted, as the baseline every S has: involutive coincidences v = v^-1 (v != reverse-and-flip(v) as words),
i.e. the beta = identity case, and all coincidences (distinct values vs words) per length.

Usage:
  twist.py sol FILE --alpha CONJ_INDEX_OR_MAT --r R          census of a solution file (alpha as used by haar_sym)
  twist.py randorb GROUP... N_CYC --k2 m f --samples M ...   census + cost of M random beta-invariant S
  twist.py randsample GROUP... N_CYC --d D_ ...              same for random S (beta = identity census only)
Run with -h for the options.
"""
import argparse, sys, time, math, json
import numpy as np
from hgroups import Group, parse_group, read_solution, MatGroup

# ---------------------------------------------------------------------------------------------------------------
def perm_inverse(p):
    q = np.empty_like(p)
    q[p] = np.arange(len(p))
    return q


class Haar:
    def __init__(self, G, S):
        self.G, self.S, self.d = G, list(S), len(S)
        self.L = [G.left_perm(s) for s in S]          # g -> s g      (A -> B)
        self.Li = [perm_inverse(p) for p in self.L]    # g -> s^-1 g   (B -> A)

    def ball(self, D, startB=False):
        """cumulative reached counts per BFS step from (e,A) (or (e,B)); returns (levels, reached sets per side)."""
        N = self.G.N
        V = [np.zeros(N, bool), np.zeros(N, bool)]
        side = 1 if startB else 0
        fr = np.zeros(N, bool); fr[self.G.ident] = True; V[side][self.G.ident] = True
        levels = []
        for step in range(D - 1):
            T = self.L if side == 0 else self.Li
            nxt = np.zeros(N, bool)
            idx = np.nonzero(fr)[0]
            for t in T:
                nxt[t[idx]] = True
            ns = side ^ 1
            nxt &= ~V[ns]
            V[ns] |= nxt
            levels.append(int(V[ns].sum()))
            fr, side = nxt, ns
        return levels, V

    def cost(self, D):
        N = self.G.N
        if D % 2 == 0:
            lev, V = self.ball(D)
            return N - int(V[1].sum()), lev, V
        levA, VA = self.ball(D)
        levB, VB = self.ball(D, startB=True)
        return (N - int(VA[0].sum())) + (N - int(VB[1].sum())), levA, (VA, VB)

    def words(self, length, first_sign):
        """values and letter arrays of all reduced alternating words of a given length.
        first_sign = +1: v = s_{i1} s_{i2}^-1 s_{i3} ...  (as a product read left to right)."""
        d = self.d
        # build left to right: value = x_1 x_2 ... ; append on the right: val * y  ==  (y^-1 ... ) is awkward with
        # left-multiplication tables, so build right to left: v = x_1 (x_2 (... x_L)), each step a left multiplication.
        signs = [first_sign * (1 if t % 2 == 0 else -1) for t in range(length)]
        # start with the last letter
        lt = signs[-1]
        Sv = np.array(self.S)
        invS = self.G.inv_perm()[Sv]
        vals = (Sv if lt > 0 else invS).copy()
        letters = np.arange(d)[:, None]
        for t in range(length - 2, -1, -1):
            sg = signs[t]
            nv, nl = [], []
            for i in range(d):
                keep = letters[:, 0] != i
                tab = self.L[i] if sg > 0 else self.Li[i]
                nv.append(tab[vals[keep]])
                nl.append(np.hstack([np.full((keep.sum(), 1), i), letters[keep]]))
            vals = np.concatenate(nv)
            letters = np.vstack(nl)
        return vals, letters


def census(H, beta, sigma, maxlen):
    """twisted and involutive coincidences of even subwords up to maxlen."""
    G = H.G
    inv = G.inv_perm()
    out = {}
    for L in range(2, maxlen + 1, 2):
        tw = inv_c = tot = 0
        for fs in (1, -1):
            vals, let = H.words(L, fs)
            tot += len(vals)
            rev = let[:, ::-1]
            # beta* (twisted) coincidence: beta(v) = v^-1, excluding sigma-palindromes
            if beta is not None:
                anti = beta[vals] == inv[vals]
                pal = np.all(let == sigma[rev], axis=1)
                tw += int(np.sum(anti & ~pal))
            # involutive coincidence: v = v^-1, excluding palindromes
            invo = vals == inv[vals]
            pal0 = np.all(let == rev, axis=1)
            inv_c += int(np.sum(invo & ~pal0))
        out[L] = dict(words=tot, twisted=tw, involutive=inv_c,
                      twisted_relators=tw / (4 * L), involutive_relators=inv_c / (4 * L))
    return out


def distinct_by_length(H, maxlen):
    """number of words and distinct values per exact length (sign pattern starting with +, i.e. side B for odd)."""
    res = {}
    for L in range(1, maxlen + 1):
        vals, _ = H.words(L, 1)
        res[L] = (len(vals), int(len(np.unique(vals))))
    return res


def shots(H, ell):
    """n_x = number of non-backtracking walks of length exactly ell from (e,A) to each x on the final side."""
    G, d, N = H.G, H.d, H.G.N
    cnt = np.zeros((d, N), np.int64)
    for i in range(d):
        cnt[i, H.L[i][G.ident]] += 1
    side = 1
    for step in range(1, ell):
        T = H.L if side == 0 else H.Li
        new = np.zeros((d, N), np.int64)
        tot = cnt.sum(axis=0)
        for j in range(d):
            src = tot - cnt[j]               # walks not ending with letter j (no immediate backtrack)
            np.add.at(new[j], T[j], src)     # new[j][T[j][g]] += src[g]
        cnt, side = new, side ^ 1
    return cnt.sum(axis=0)


def alpha_perm(G, conj=None, r=1, frob=None):
    """beta(x) = (g x g^-1) x (z -> r z), or a Frobenius power on the matrix entries."""
    n, N = G.n, G.N
    allg = np.arange(N)
    xq, z = allg // n, allg % n
    Q = G.Q
    if frob is not None:
        yq = Q.frob_vec(xq, frob)
    elif conj is not None:
        gi = Q.inv_vec(np.array([conj]))[0]
        yq = Q.mul_vec(Q.mul_vec(np.full(N, conj), xq), np.full(N, gi))
    else:
        yq = xq
    return yq * n + (r * z) % n


def swapconj_cube(G, cdesc, r3):
    """beta = alpha^3 for alpha(x1, x2, z) = (c x2 c^-1, x1, r z) on prod G G x Z_n with c^3 = 1:
    alpha^3(x1, x2, z) = (c^2 x2 c^-2, c x1 c^-1, r^3 z)."""
    import re
    Q, n, N = G.Q, G.n, G.N
    g1, o2 = Q.g1, Q.g2.order
    c = g1.find(*map(int, re.match(r"mat\((\d+),(\d+),(\d+),(\d+)\)", cdesc).groups()))
    c2 = int(g1.mul_vec(np.array([c]), np.array([c]))[0])
    ci = int(g1.inv_vec(np.array([c]))[0]); c2i = int(g1.inv_vec(np.array([c2]))[0])
    allg = np.arange(N)
    xq, z = allg // n, allg % n
    x1, x2 = xq // o2, xq % o2
    y1 = g1.mul_vec(g1.mul_vec(np.full(N, c2), x2), np.full(N, c2i))
    y2 = g1.mul_vec(g1.mul_vec(np.full(N, c), x1), np.full(N, ci))
    return (y1 * o2 + y2) * n + (r3 * z) % n


def sigma_of(S, beta):
    pos = {s: i for i, s in enumerate(S)}
    return np.array([pos.get(int(beta[s]), -1) for s in S])


def find_conj(Q, spec):
    """spec: integer index (haar_sym's ALPHA index differs from ours, so prefer mat(a,b,c,d))."""
    import re
    m = re.match(r"mat\((\d+),(\d+),(\d+),(\d+)\)", spec)
    if m:
        return Q.find(*map(int, m.groups()))
    return int(spec)


def summarize(H, D, beta, sigma, maxlen=None, want_shots=False):
    ell = D - 1
    maxlen = maxlen or (ell - 1 if ell % 2 else ell)
    c, lev, _ = H.cost(D)
    cen = census(H, beta, sigma, maxlen)
    res = dict(cost=c, levels=lev, census=cen)
    if want_shots and D % 2 == 0:
        nx = shots(H, ell)
        res["shots_mean"] = float(nx.mean())
        res["shots_var"] = float(nx.var())
        res["shots_zero_exact_length"] = int((nx == 0).sum())
    return res


def random_symmetric_S(G, beta, m, f, rng, fixed_pool):
    N = G.N
    S = []
    if f >= 1:
        S.append(G.ident)
        for _ in range(f - 1):
            while True:
                x = int(fixed_pool[rng.integers(len(fixed_pool))])
                if x not in S:
                    S.append(x); break
    for _ in range(m):
        while True:
            x = int(rng.integers(N))
            y = int(beta[x])
            if x != y and x not in S and y not in S:
                S += [x, y]; break
    return S


def main():
    ap = argparse.ArgumentParser()
    sub = ap.add_subparsers(dest="mode", required=True)
    a1 = sub.add_parser("sol")
    a1.add_argument("file")
    a1.add_argument("--alpha", default=None, help="conjugating matrix mat(a,b,c,d) as in the haar_sym log")
    a1.add_argument("--frob", type=int, default=None, help="beta = entrywise Frobenius x -> x^(p^j) (matrix groups)")
    a1.add_argument("--swapconj", default=None, help="prod G G: beta = alpha^3 for alpha(x1,x2) = (c x2 c^-1, x1), c = mat(..) of order 3")
    a1.add_argument("--r", type=int, default=1, help="beta on Z_n: z -> r z (for --swapconj give r^3 of the haar run)")
    a1.add_argument("--maxlen", type=int, default=None)
    a1.add_argument("--json", default=None)
    a2 = sub.add_parser("randorb")
    a2.add_argument("group", nargs="+")
    a2.add_argument("--d", type=int, required=True)
    a2.add_argument("--D", type=int, required=True)
    a2.add_argument("--m", type=int, required=True)
    a2.add_argument("--f", type=int, default=0)
    a2.add_argument("--alpha", default=None, help="conjugating matrix mat(a,b,c,d); default: a random trace-0 / involution")
    a2.add_argument("--frob", type=int, default=None)
    a2.add_argument("--r", type=int, default=None)
    a2.add_argument("--samples", type=int, default=200)
    a2.add_argument("--seed", type=int, default=1)
    a2.add_argument("--maxlen", type=int, default=None)
    a2.add_argument("--out", default=None)
    a3 = sub.add_parser("randsample")
    a3.add_argument("group", nargs="+")
    a3.add_argument("--d", type=int, required=True)
    a3.add_argument("--D", type=int, required=True)
    a3.add_argument("--samples", type=int, default=200)
    a3.add_argument("--seed", type=int, default=1)
    a3.add_argument("--maxlen", type=int, default=None)
    a3.add_argument("--out", default=None)
    A = ap.parse_args()

    if A.mode == "sol":
        d, D, G, S = read_solution(A.file)
        if A.swapconj is not None:
            beta = swapconj_cube(G, A.swapconj, A.r)
        elif A.frob is not None:
            beta = alpha_perm(G, frob=A.frob, r=A.r)
        else:
            beta = alpha_perm(G, conj=find_conj(G.Q, A.alpha), r=A.r)
        assert np.all(beta[beta] == np.arange(G.N)), "beta is not an involution"
        # the file is normalised by s_0^-1 on the right, (g,A) -> ...: S' = S s_0^-1 is invariant under the
        # conjugate automorphism x -> s0' beta(x) ... ; recover a symmetric frame by trying all right translates
        Sarr = np.array(S)
        inv = G.inv_perm()
        best = None
        for t in [G.ident] + list(range(G.N)):
            T = G.mul_vec(Sarr, np.full(d, t))       # S t
            Bt = beta[T]
            if set(Bt.tolist()) == set(T.tolist()):
                best = T.tolist(); break
        if best is None:
            print("no right translate of S is beta-invariant; census without symmetry frame")
            Ssym = S
        else:
            Ssym = best
        H = Haar(G, Ssym)
        sigma = sigma_of(Ssym, beta)
        res = summarize(H, D, beta, sigma, A.maxlen, want_shots=True)
        res.update(file=A.file, group=G.spec, N=G.N, d=d, D=D, symmetric_frame=best is not None,
                   fix=int(np.sum(beta == np.arange(G.N))), anti=int(np.sum(beta == inv)),
                   involutions=int(np.sum(inv == np.arange(G.N))))
        print(json.dumps(res, indent=1))
        if A.json:
            json.dump(res, open(A.json, "w"), indent=1)
        return

    Q, rest = parse_group(A.group)
    n = int(rest[0]) if rest else 1
    G = Group(Q, n)
    inv = G.inv_perm()
    rng = np.random.default_rng(A.seed)
    out = open(A.out, "w") if A.out else None
    t0 = time.time()
    if A.mode == "randorb":
        if A.frob is not None:
            beta = alpha_perm(G, frob=A.frob, r=A.r if A.r is not None else 1)
        else:
            if A.alpha is None:
                # trace-0 element (order 4 in SL, involution in PSL), as haar_sym's random choice of an order-2 conjugation
                tr = Q.trace(np.arange(Q.order))
                cands = np.nonzero(tr == 0)[0]
                conj = int(cands[0])
            else:
                conj = find_conj(Q, A.alpha)
            r = A.r
            if r is None:
                r = 1
                if n > 1:   # r of order 2 with the fewest fixed points, smallest first (haar_sym's rule)
                    bestfx = None
                    for rr in range(1, n):
                        if math.gcd(rr, n) != 1 or (rr * rr) % n != 1 % n:
                            continue
                        fx = n if rr == 1 else math.gcd(rr - 1, n)
                        if bestfx is None or fx < bestfx:
                            bestfx, r = fx, rr
            beta = alpha_perm(G, conj=conj, r=r)
        assert np.all(beta[beta] == np.arange(G.N))
        fixed = np.nonzero(beta == np.arange(G.N))[0]
        fixed_pool = fixed[fixed != G.ident]
        hdr = dict(group=G.spec, N=G.N, d=A.d, D=A.D, m=A.m, f=A.f, fix=len(fixed), anti=int(np.sum(beta == inv)),
                   involutions=int(np.sum(inv == np.arange(G.N))), r=None if A.frob is not None else r,
                   alpha=None if A.frob is not None else Q.desc(conj), frob=A.frob)
        print(json.dumps(hdr))
        if out:
            out.write(json.dumps(dict(header=hdr)) + "\n")
        for t in range(A.samples):
            S = random_symmetric_S(G, beta, A.m, A.f, rng, fixed_pool)
            H = Haar(G, S)
            sigma = sigma_of(S, beta)
            res = summarize(H, A.D, beta, sigma, A.maxlen)
            res["S"] = S
            if out:
                out.write(json.dumps(res) + "\n"); out.flush()
        print(f"done {A.samples} samples in {time.time() - t0:.1f}s")
    else:
        for t in range(A.samples):
            S = [G.ident] + [int(x) for x in rng.choice(G.N, A.d - 1, replace=False) if x != G.ident][: A.d - 1]
            while len(S) < A.d:
                x = int(rng.integers(G.N))
                if x not in S:
                    S.append(x)
            H = Haar(G, S)
            res = summarize(H, A.D, None, None, A.maxlen)
            res["S"] = S
            if out:
                out.write(json.dumps(res) + "\n"); out.flush()
        print(f"done {A.samples} samples in {time.time() - t0:.1f}s")


if __name__ == "__main__":
    main()
