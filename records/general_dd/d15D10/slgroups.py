"""Semilinear x Z_k candidates: G = (F_p^2 x| (Z_n x| Z_2)) x Z_k, N = 2 n p^2 k, n | p^2-1 (cay_mgk header p,-2n,k)."""
import random, struct
import nc_enum as E, build_q as B
def isprime(n): return n > 1 and all(n % i for i in range(2, int(n ** .5) + 1))
def supply(lo, hi, kmax, nmin=20, pmax=8000):
    out = []
    for p in range(7, pmax):
        if not isprime(p): continue
        q = p * p
        for k in range(1, kmax + 1):
            for n in range(max(nmin, lo // (2 * q * k)), hi // (2 * q * k) + 2):
                N = 2 * n * q * k
                if lo <= N <= hi and (q - 1) % n == 0: out.append((N, p, n, k))
    return out
def mulmat(z, p, eps): return (z[0] % p, (eps * z[1]) % p, z[1] % p, z[0] % p)
def build(gdir, p, n, k, rng, nz=2):
    eps = next(e for e in range(2, p) if pow(e, (p - 1) // 2, p) == p - 1)
    s = E.sample_2d_singer(p, n, rng, tries=200)
    if not s: return []
    M = tuple(s['P1']); S = (1, 0, 0, p - 1); out = []; seen = set()
    for z in [(1, 0)] + [(rng.randrange(p), rng.randrange(1, p)) for _ in range(nz * 4)]:
        els = B.enum_group(p, [M, B.mm(S, mulmat(z, p, eps), p)], 2 * n + 2)
        if not els or len(els) != 2 * n: continue
        key = frozenset(els)
        if key in seen: continue
        seen.add(key); f = f'{gdir}/slk_{p}_{n}_{z[0]}_{z[1]}_k{k}.bin'
        with open(f, 'wb') as fh:
            fh.write(struct.pack('iii', p, -len(els), k))
            for e in els: fh.write(struct.pack('iiii', *e))
        out.append(f)
        if len(out) >= nz: break
    return out
