"""c5 helpers: LPS(p) x Z_m covers over PGL(2,q) with labels; cost = unreached-within-D vertices from both starts.
Same generator conventions as research/theorems/haar_families/gen_lps_cover.py (copied, not imported: that module runs main())."""
import subprocess, re, math, random
HAAR = '/home/user/degree-diameter/research/theorems/haar_families/haar_ecc'

def isqrt(n):
    r = int(n ** .5)
    while r * r > n: r -= 1
    while (r + 1) * (r + 1) <= n: r += 1
    return r

def lps_set(p):
    S = []
    R = isqrt(p) + 1
    for a0 in range(-R, R + 1):
        for a1 in range(-R, R + 1):
            for a2 in range(-R, R + 1):
                r2 = p - a0*a0 - a1*a1 - a2*a2
                if r2 < 0: continue
                a3 = isqrt(r2)
                if a3 * a3 != r2: continue
                for b3 in ([a3, -a3] if a3 else [0]):
                    if p % 4 == 1: ok = a0 > 0 and a0 % 2 == 1 and a1 % 2 == 0 and a2 % 2 == 0 and b3 % 2 == 0
                    else: ok = a0 % 2 == 0 and a1 % 2 and a2 % 2 and b3 % 2 and (a0 > 0 or (a0 == 0 and a1 > 0))
                    if ok: S.append((a0, a1, a2, b3))
    assert len(S) == p + 1
    return S

def xy(q):
    for a in range(q):
        for b in range(q):
            if (a*a + b*b + 1) % q == 0: return a, b

class Lps:
    def __init__(self, p, q):
        self.p, self.q = p, q
        self.S = lps_set(p)
        x, y = xy(q)
        self.mats = []
        for a0, a1, a2, a3 in self.S:
            self.mats.append(((a0 + a1*x + a3*y) % q, (-a1*y + a2 + a3*x) % q, (-a1*y - a2 + a3*x) % q, (a0 - a1*x - a3*y) % q))
        Sset = set(self.S)
        def norm_rep(al):
            if al in Sset: return al
            return tuple(-t for t in al)
        sig = lambda al: (al[0], al[3], al[1], al[2])
        self.index = {al: i for i, al in enumerate(self.S)}
        seen = set(); self.cycles = []; self.fixed = []
        for al in sorted(self.S):
            if al in seen: continue
            b = norm_rep(sig(al))
            if b == al: self.fixed.append(self.index[al]); seen.add(al); continue
            c = [al, b, norm_rep(sig(b))]
            seen |= set(c)
            self.cycles.append([self.index[e] for e in c])

    def roots(self, m):
        if m <= 3: return []
        return [r for r in range(2, m) if (r*r + r + 1) % m == 0]

    def cyc_labels(self, m, r, ts):
        lab = [0] * (self.p + 1)
        for c, t in zip(self.cycles, ts):
            for e, i in enumerate(c): lab[i] = t * pow(r, e, m) % m
        return lab

def gen_text(L, m, labels):
    return '\n'.join(' '.join(map(str, list(M) + [z])) for M, z in zip(L.mats, labels)) + '\n'

def run(q, m, text, D=None):
    """haar_ecc pgl q m -p [-D D]; returns dict with comp sizes, eccs and profiles."""
    cmd = [HAAR, 'pgl', str(q), str(m), '-p'] + (['-D', str(D)] if D else [])
    r = subprocess.run(cmd, input=text, capture_output=True, text=True)
    out = r.stdout
    res = {}
    mm = re.search(r'ecc_A=(\d+) ecc_B=(\d+) compA=(\d+) compB=(\d+) .*diam=(\d+)', out)
    if mm: res['eA'], res['eB'], res['cA'], res['cB'], res['diam'] = map(int, mm.groups())
    pa = re.search(r'profile \(e,A\):(.*)', out); pb = re.search(r'profile \(e,B\):(.*)', out)
    if pa: res['pA'] = list(map(int, pa.group(1).split()))
    if pb: res['pB'] = list(map(int, pb.group(1).split()))
    res['ok'] = 'cA' in res
    return res

def cost(L, q, m, labels, D):
    """0 iff the component of (I,A) and of (I,B) both have V = q(q^2-1)m vertices, all within distance D.
    Returns (cost, diam_or_None, cA, cB)."""
    V = q * (q*q - 1) * m
    res = run(q, m, gen_text(L, m, labels), D)
    if not res['ok']: return (10**12, None, 0, 0)
    reachA = sum(res['pA']); reachB = sum(res['pB'])
    c = max(0, V - reachA) + max(0, V - reachB)
    return c, res['diam'], res['cA'], res['cB'], res

def V_of(q, m): return q * (q*q - 1) * m
