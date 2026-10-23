"""BEYOND_RANDOM.md §2: which binding words coincide, for random S and for alpha-invariant S.
For each sampled S, enumerate the reduced alternating words of one side up to length Lmax, count distinct values per
length, and classify every coinciding pair (w1, w2) by a canonical letter pattern.

usage: python3 collisions.py FAM p e n d D_side_len Lmax samples MODE [MODE...]
  MODE = rand | conj | frob | frob_noinv | conj2 | frob2   (conj2, frob2: k = 2; others k = 3; frob_noinv: fixed generators that are not involutions; f fixed generators as haar_sym: f = 1, 2, 3 for d = 1, 2, 0 mod 3)
example: python3 collisions.py sl 2 3 43 8 4 200 rand conj frob"""
import sys, random, collections
from symgroups import QxZ, Conj, Frob, find_order3_conj, unit_order3, fixed_points

def words(d, L, first_sign):
    """reduced alternating words of length L: index tuples (i_1..i_L), consecutive indices differ."""
    if L == 0: yield (); return
    def rec(w):
        if len(w) == L: yield tuple(w); return
        for i in range(d):
            if not w or i != w[-1]: yield from rec(w + [i])
    yield from rec([])

def value(G, S, Sinv, w, first_sign):
    """s_{i_L}^{e_L} ... s_{i_1}^{e_1}, signs alternating starting with first_sign (+1: A-word)."""
    x = G.e(); sgn = first_sign
    for i in w:
        x = G.mul(S[i] if sgn > 0 else Sinv[i], x); sgn = -sgn
    return x

def find_order4(G, rng):
    """g with g^2 central but g not central (conjugation of order 2)."""
    m1 = G.norm(G.F.neg[1], 0, 0, G.F.neg[1]) + (0,)
    while True:
        g = G.rand(rng)[:4] + (0,); g2 = G.mul(g, g)
        if g != G.e() and g != m1 and g2 in (G.e(), m1): return g

def make_S(G, mode, d, rng, alpha=None, fix=None):
    k = 2 if mode.endswith('2') else 3
    f = {1: 1, 2: 2, 0: 3}[d % 3] if k == 3 else (1 if d % 2 else 2); m = (d - f) // k
    if mode == 'rand':
        S = [G.e()]
        while len(S) < d:
            x = G.rand(rng)
            if x not in S: S.append(x)
        return S, ['e'] + ['r%d' % i for i in range(1, d)]
    S = [G.e()]; lab = ['e']
    while len(S) < f:
        x = rng.choice(fix)
        if x not in S: S.append(x); lab.append('F%d' % len(S))
    for j in range(m):
        while True:
            x = G.rand(rng); o = [x]
            while len(o) < k: o.append(alpha(o[-1]))
            if len(set(o)) == k and alpha(o[-1]) == x and not set(o) & set(S): break
        S += o; lab += ['o%d.%d' % (j, i) for i in range(k)]
    return S, lab

def pattern(w, lab, ren=None, ph=None):
    """canonical pattern: orbits renamed in order of first appearance, phases relative to the first appearance.
    Pass the same ren/ph dicts for both words of a pair so that the pair is canonicalised jointly."""
    ren = {} if ren is None else ren; ph = {} if ph is None else ph; out = []
    for i in w:
        l = lab[i]
        if l[0] == 'o':
            j, p = l[1:].split('.'); p = int(p)
            if j not in ren: ren[j] = 'abcdefgh'[len(ren)]; ph[j] = p
            out.append('%s%d' % (ren[j], (p - ph[j]) % 3))   # (mod 3 also labels k = 2 phases 0/1 correctly)
        else: out.append(l)
    return out

def run(G, mode, d, Lmax, samples, seed=1):
    rng = random.Random(seed); alpha = fix = None
    if mode in ('conj2', 'frob2'):              # involutive alpha: conjugation by g with g^2 central, or Frobenius of order 2
        r = G.n - 1 if G.n > 1 else 0
        alpha = Conj(G, find_order4(G, rng), r) if mode == 'conj2' else Frob(G, G.F.e // 2, r)
        fix = [x for x in fixed_points(G, alpha) if x != G.e()]
    elif mode != 'rand':
        r = unit_order3(G.n)
        alpha = Conj(G, find_order3_conj(G, rng), r) if mode == 'conj' else Frob(G, 1, r)
        fix = [x for x in fixed_points(G, alpha) if x != G.e()]
        if mode == 'frob_noinv': fix = [x for x in fix if G.mul(x, x) != G.e()]
    pats = collections.Counter(); lost = []; W = 0
    for s in range(samples):
        S, lab = make_S(G, mode, d, rng, alpha, fix); Sinv = [G.inv(x) for x in S]
        for side, fs in (('A', 1), ('B', -1)):
            seen = {}; W = 0
            for L in range(Lmax + 1):
                if L % 2 != Lmax % 2: continue
                for w in words(d, L, fs):
                    v = value(G, S, Sinv, w, fs); W += 1
                    if v in seen:
                        ren, ph = {}, {}
                        pats[(side, ' '.join(pattern(seen[v], lab, ren, ph)) + ' = ' + ' '.join(pattern(w, lab, ren, ph)))] += 1
                    else: seen[v] = w
            lost.append(1 - len(seen) / W)
    return pats, sorted(lost), W, (len(fix) if fix is not None else 0)

if __name__ == '__main__':
    fam, p, e, n, d, Lmax, samples = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]), int(sys.argv[5]), int(sys.argv[6]), int(sys.argv[7])
    G = QxZ(fam, p, e, n)
    print('group %s(2,%d^%d) x Z_%d, N = %d, d = %d, words of length <= %d with parity %d, %d samples x 2 sides' % (
        fam, p, e, n, G.order(), d, Lmax, Lmax % 2, samples))
    print('%-11s %8s %8s %8s %8s %8s %8s' % ('mode', '|Fix|-1', 'words', 'p10', 'median', 'mean', 'p90'))
    allp = {}
    for mode in sys.argv[8:]:
        pats, lost, W, nfix = run(G, mode, d, Lmax, samples)
        q = lambda t: 100 * lost[int(t * (len(lost) - 1))]
        print('%-11s %8d %8d %7.2f%% %7.2f%% %7.2f%% %7.2f%%' % (mode, nfix, W, q(0.1), q(0.5), 100 * sum(lost) / len(lost), q(0.9)))
        allp[mode] = pats
    for mode, pats in allp.items():
        print('\n%s: most common coinciding pairs (count per sample, both sides; letters i_1 i_2 ...):' % mode)
        for (side, pt), c in pats.most_common(8): print('    %.3f  %s: %s' % (c / samples, side, pt))
