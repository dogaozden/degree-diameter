# c2: GF(2^18) model of W(5,8)/Q(6,8) points, torus T = norm-1 group of F_{512^2}/F_8 (order 513).
# Abstract form: omega(x,y) = Tr_{512/8}( Tr_{512^2/512}( x * y^512 ) ), alternating F_8-form on F_{2^18}, 6-dim over F_8.
# Points = F_{2^18}^* / F_8^*  <->  classes L in Z_37449 (x = g^L).  Translation by 73*t <-> element of T.
import numpy as np, os
N2 = 2**18 - 1           # 262143
NP = N2 // 7             # 37449 points
POLY = (1 << 18) | (1 << 7) | 1   # x^18 + x^7 + 1 (checked primitive below)

def build():
    exp = np.zeros(N2, dtype=np.int64)
    x = 1
    for i in range(N2):
        exp[i] = x
        x <<= 1
        if x >> 18:
            x ^= POLY
    log = np.full(1 << 18, -1, dtype=np.int64)
    log[exp] = np.arange(N2)
    assert (log[1:] >= 0).all() and len(set(exp.tolist())) == N2, "poly not primitive"
    return exp, log

if os.path.exists('/tmp/_nonexistent_'):
    pass

EXP, LOG = build()
# F_512 = {0} U {g^{513k}}; trace to F_8: Tr(u)=u+u^8+u^64
F512 = np.concatenate([[0], EXP[np.arange(0, N2, 513)]])
VAL = np.zeros(1 << 18, dtype=np.int64)        # Tr_{512/8}(u) for u in F_512 (value in F_8 subset of field)
def _pow(u, k):
    return EXP[(LOG[u] * k) % N2] if u else 0
for u in F512:
    u = int(u)
    if u == 0: continue
    VAL[u] = u ^ _pow(u, 8) ^ _pow(u, 64)
NZ = VAL != 0   # True iff omega nonzero (for u != 0); VAL[0]=0 so omega=0 when u=0

F8 = np.concatenate([[0], EXP[np.arange(0, N2, 37449)]])  # 8 elements of F_8 inside GF(2^18)

def omega_val(a, b):
    """omega between point classes a, b (int arrays): field element in F_8 (as GF(2^18) int)."""
    a = np.asarray(a, dtype=np.int64); b = np.asarray(b, dtype=np.int64)
    e = (a + 512 * b) % N2
    u = EXP[e] ^ EXP[(512 * e) % N2]
    return VAL[u]

def nonorth(a, b):
    a = np.asarray(a, dtype=np.int64); b = np.asarray(b, dtype=np.int64)
    e = (a + 512 * b) % N2
    u = EXP[e] ^ EXP[(512 * e) % N2]
    return NZ[u]

if __name__ == '__main__':
    import random
    random.seed(1)
    # sanity: alternating, symmetric, and T-invariance (translation by 73t)
    bad = 0
    for _ in range(20000):
        a = random.randrange(NP); b = random.randrange(NP); t = random.randrange(513)
        assert nonorth(a, a) == False
        assert bool(nonorth(a, b)) == bool(nonorth(b, a))
        assert bool(nonorth(a, b)) == bool(nonorth((a + 73 * t) % NP, (b + 73 * t) % NP))
    print('primitive ok; symmetric/alternating/T-invariant checks ok')
    # density of non-orthogonal pairs (should be 7/8 = 0.875 for a random pair)
    a = np.random.randint(0, NP, 200000); b = np.random.randint(0, NP, 200000)
    print('nonorth density', nonorth(a, b).mean())
    print('omega values in F8?', set(np.unique(omega_val(a[:5000], b[:5000])).tolist()) <= set(F8.tolist()))
