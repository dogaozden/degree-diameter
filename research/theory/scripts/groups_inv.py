"""Center size and involution counts of the record groups (needed for the special-target terms of THRESHOLD.md §3.4).
Formulas for SL/PSL/PGL(2,q) are checked by brute force for small q in selftest()."""
import itertools, math

# 'comm' = |G'| (order of the commutator subgroup); q >= 4 throughout.
def sl2(q):
    if q % 2 == 0: return dict(order=q*(q*q-1), Z=1, inv=q*q-1, inv_c=0, comm=q*(q*q-1))
    return dict(order=q*(q*q-1), Z=2, inv=1, inv_c=1, comm=q*(q*q-1))

def psl2(q):
    if q % 2 == 0: return sl2(q)
    i = q*(q+1)//2 if q % 4 == 1 else q*(q-1)//2
    return dict(order=q*(q*q-1)//2, Z=1, inv=i, inv_c=0, comm=q*(q*q-1)//2)

def pgl2(q):
    if q % 2 == 0: return sl2(q)
    return dict(order=q*(q*q-1), Z=1, inv=q*q, inv_c=0, comm=q*(q*q-1)//2)

def cyc(m):
    return dict(order=m, Z=m, inv=1 if m % 2 == 0 else 0, inv_c=1 if m % 2 == 0 else 0, comm=1)

def prod(*gs):
    o = math.prod(g['order'] for g in gs); Z = math.prod(g['Z'] for g in gs)
    sq = math.prod(g['inv'] + 1 for g in gs) - 1          # x^2 = e, x != e
    sqc = math.prod(g['inv_c'] + 1 for g in gs) - 1       # central ones
    return dict(order=o, Z=Z, inv=sq, inv_c=sqc, comm=math.prod(g.get('comm', 0) for g in gs))

def meta(m, k, r):
    """Z_m x| Z_k, b a b^-1 = a^r; elements a^i b^j, (i,j)(i',j') = (i + r^j i', j + j')."""
    assert pow(r, k, m) == 1 % m
    rp = [pow(r, j, m) for j in range(k)]
    mul = lambda x, y: ((x[0] + rp[x[1]] * y[0]) % m, (x[1] + y[1]) % k)
    G = [(i, j) for i in range(m) for j in range(k)]
    gens = [(1, 0), (0, 1)]
    Z = [g for g in G if all(mul(g, h) == mul(h, g) for h in gens)]
    inv = [g for g in G if g != (0, 0) and mul(g, g) == (0, 0)]
    Zs = set(Z)
    return dict(order=m*k, Z=len(Z), inv=len(inv), inv_c=sum(1 for g in inv if g in Zs), comm=m // math.gcd(m, r - 1),
                metabelian=True)

def from_table_name(name):
    """d5 table groups (research/d5/tables/*.txt names)."""
    if name == 'sl_11': return sl2(11)
    if name == 'pgl_3__x__cyc_24': return dict(prod(dict(order=24, Z=1, inv=9, inv_c=0, comm=12), cyc(24)), metabelian=True)  # S_4
    if name == 'agl_7__x__cyc_21': return dict(prod(dict(order=42, Z=1, inv=7, inv_c=0, comm=7), cyc(21)), metabelian=True)  # AGL(1,7)
    if name == 'heis_5__x__cyc_7': return dict(prod(dict(order=125, Z=5, inv=0, inv_c=0, comm=5), cyc(7)), metabelian=True)
    if name == 'heis_11': return dict(order=1331, Z=11, inv=0, inv_c=0, comm=11, metabelian=True)
    return None

def from_header(h):
    """frontier/sols header tokens after 'd D': family args ... n m N order."""
    t = h[2:h.index('n')]; m = int(h[h.index('n') + 1])
    def one(tok):
        fam, q = tok[0], int(tok[1]); rest = tok[2:]
        if rest[:1] == ['poly']: rest = rest[2:]
        g = dict(sl=sl2, psl=psl2, pgl=pgl2)[fam](q)
        return g, rest
    if t[0] == 'prod':
        g1, rest = one(t[1:]); g2, rest = one(rest); g = prod(g1, g2)
    elif t[0] == 'meta':
        g = meta(int(t[1]), int(t[2]), int(t[3]))
    else:
        g, _ = one(t)
    return prod(g, cyc(m)) if m > 1 else g

# ---------- brute-force check of the SL/PSL/PGL formulas for small prime q ----------
def _mats(p):
    return [(a, b, c, d) for a in range(p) for b in range(p) for c in range(p) for d in range(p)]
def selftest():
    for p in (3, 5, 7, 11, 13):
        mm = lambda x, y: ((x[0]*y[0]+x[1]*y[2]) % p, (x[0]*y[1]+x[1]*y[3]) % p, (x[2]*y[0]+x[3]*y[2]) % p, (x[2]*y[1]+x[3]*y[3]) % p)
        I = (1, 0, 0, 1)
        GL = [x for x in _mats(p) if (x[0]*x[3]-x[1]*x[2]) % p]
        SL = [x for x in GL if (x[0]*x[3]-x[1]*x[2]) % p == 1]
        scal = lambda x: x[1] == 0 and x[2] == 0 and x[0] == x[3]
        sl_inv = sum(1 for x in SL if x != I and mm(x, x) == I)
        psl_inv = sum(1 for x in SL if not scal(x) and scal(mm(x, x))) // 2       # classes {x,-x}
        pgl_inv = sum(1 for x in GL if not scal(x) and scal(mm(x, x))) // (p - 1)
        assert sl_inv == sl2(p)['inv'], (p, sl_inv)
        assert psl_inv == psl2(p)['inv'], (p, psl_inv)
        assert pgl_inv == pgl2(p)['inv'], (p, pgl_inv)
    print('groups_inv selftest OK (SL, PSL, PGL(2,p), p = 3..13)')

if __name__ == '__main__':
    selftest()
