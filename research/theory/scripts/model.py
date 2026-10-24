"""The Poisson model of THRESHOLD.md §3.4-3.5 for a concrete group: mu = sum over target classes of exp(-lambda_x), with
 (i) special targets for odd D (inverse pairs, involutions, central rotation orbits) and
 (ii) the first-order coincidence loss of words: junction swaps a b^-1 = b a^-1 (prob tau_inv = #{x != e: x^2 = e}/(N-1))
      and sign-preserving rearrangements, which agree in G^ab and so coincide with prob ~ 1/|G'| (Q x Z_m families only)."""
import math, functools, itertools, random

def Wlen(d, L): return 1 if L == 0 else d * (d - 1) ** (L - 1)
def lengths(D): return [L for L in range(D) if L % 2 == (D - 1) % 2]
def W(d, D): return sum(Wlen(d, L) for L in lengths(D))

@functools.lru_cache(None)
def rearr_mean(d, L, samples=400, seed=1):
    """Mean number of reduced alternating words with the same multiset of +letters and of -letters (incl. the word)."""
    if L <= 1: return 1.0
    rng = random.Random(seed * 1000 + d * 31 + L); tot = 0
    for _ in range(samples):
        w = [rng.randrange(d)]
        while len(w) < L: w.append(rng.choice([x for x in range(d) if x != w[-1]]))
        pl, mi = w[0::2], w[1::2]; c = 0
        for p in set(itertools.permutations(pl)):
            for m in set(itertools.permutations(mi)):
                v = [None] * L; v[0::2] = p; v[1::2] = m
                if all(v[i] != v[i + 1] for i in range(L - 1)): c += 1
        tot += c
    return tot / samples

def W_eff(d, D, N, g, coincid=True):
    if not coincid or g is None: return float(W(d, D))
    tau_inv = g['inv'] / (N - 1)
    tau_re = 0.0 if g.get('metabelian') else max(1.0 / g['comm'] - 1.0 / N, 0.0)
    out = 0.0
    for L in lengths(D):
        j = 0 if L <= 1 or (D % 2 == 1 and L == 2) else L - 1      # junction swaps (L = 2, odd D: the swap is the inverse)
        loss = (j * tau_inv + (rearr_mean(d, L) - 1) * tau_re) / 2 if L >= 2 else 0.0
        out += Wlen(d, L) * max(1 - loss, 0.0)
    return out

def mu_model(d, D, N, g, coincid=True, special=True):
    """Return (mu, parts) with parts = dict of the Poisson-mean contributions."""
    we = W_eff(d, D, N, g, coincid)
    if D % 2 == 0 or g is None or not special:
        return N * math.exp(-we / N), dict(generic=N * math.exp(-we / N))
    k = (D - 1) // 2; scale = we / W(d, D)
    Z, I, Ic = g['Z'], g['inv'], g['inv_c']; Inc = I - Ic
    rot = scale * sum(Wlen(d, 2 * j) / j for j in range(1, k + 1)) / N
    parts = dict(generic=(N - Z - Inc) * math.exp(-we / N), involutions=2 * Inc * math.exp(-we / (2 * N)),
                 central=(Z - 1 - Ic) / 2 * math.exp(-rot), central_inv=Ic * math.exp(-rot / 2))
    return sum(parts.values()), parts
