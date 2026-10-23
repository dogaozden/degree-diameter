"""Haar-graph search for the bipartite degree-diameter problem, d=6, D=5 (numpy only).

CONSTRUCTION.  Take a finite group G of order N and a connection set S of 6 elements.  Vertices A(g) and
B(g) for g in G, with edges A(g) ~ B(s*g) for s in S.  This is a 6-regular bipartite graph on 2N vertices.
Right multiplication by any h in G is an automorphism (A(g) -> A(g*h), B(g) -> B(g*h)), so all A-vertices are
equivalent and all B-vertices are equivalent.  Hence diameter <= 5 iff BFS of radius 5 from A(e) and from B(e)
reaches every vertex.

Groups used: non-abelian metacyclic Z_m x|_r Z_k (orders 331..380) and the Heisenberg group mod 7 (order 343).
Any valid graph with N >= 343 has 2N >= 686 > 684 vertices.  Search is simulated annealing on the cost
(number of unreached vertices from A(e) and B(e)), round-robin over groups with persistent states.  Every
returned graph is checked with lib.is_valid.  Fallbacks: a checked order-660 Haar graph, then small trivial graphs.
"""
import itertools
import math
import time

import numpy as np

import lib


TARGET = (6, 5)
DEG = 6
DIAM = 5
N_RECORD_BEAT = 343   # Haar order N gives 2N vertices; 2N > 684 requires N >= 343
N_LO = 331
N_HI = 380
MAX_SPECS = 40
SLICE = 0.4           # seconds per group per round-robin turn
STALL = 3000          # non-improving moves before a restart
TEMP = 0.8


# ----------------------------------------------------------------------------- group tables

def meta_table(m, k, r):
    """Z_m x|_r Z_k, element (a, j) -> index a*k + j, (a, j)(b, l) = (a + r^j b, j + l). Needs r^k = 1 mod m."""
    if pow(r, k, m) != 1 % m:
        raise ValueError("bad metacyclic parameters")
    N = m * k
    pw = np.array([pow(r, j, m) for j in range(k)], dtype=np.int64)
    g = np.arange(N, dtype=np.int64)
    a, j = g // k, g % k
    MT = np.empty((N, N), dtype=np.int32)
    for lo in range(0, N, 128):
        hi = min(N, lo + 128)
        MT[lo:hi] = ((a[lo:hi, None] + pw[j[lo:hi], None] * a[None, :]) % m) * k \
            + (j[lo:hi, None] + j[None, :]) % k
    inv = np.argmax(MT == 0, axis=1).astype(np.int64)
    return MT, inv


def heis_table(p):
    """Heisenberg group mod p, order p^3, (a,b,c)(a',b',c') = (a+a', b+b', c+c'+a*b'). Identity has index 0."""
    e = np.array(list(itertools.product(range(p), repeat=3)), dtype=np.int64)
    N = len(e)
    MT = np.empty((N, N), dtype=np.int32)
    for i in range(N):
        a, b, _ = e[i]
        pa = (a + e[:, 0]) % p
        pb = (b + e[:, 1]) % p
        pc = (e[i, 2] + e[:, 2] + a * e[:, 1]) % p
        MT[i] = pa * p * p + pb * p + pc
    inv = np.argmax(MT == 0, axis=1).astype(np.int64)
    return MT, inv


def _make(spec):
    if spec[0] == "meta":
        return meta_table(spec[1], spec[2], spec[3])
    return heis_table(spec[1])


def _specs():
    """Candidate non-abelian groups, ordered: orders >= 343 first (ascending), then the rest."""
    out = []
    for N in range(N_LO, N_HI + 1):
        if N == 343:
            out.append(("heis", 7, 343))
        for k in range(2, N):
            if N % k:
                continue
            m = N // k
            if m < 3:
                continue
            rs = [r for r in range(2, m) if math.gcd(r, m) == 1 and r != 1 and pow(r, k, m) == 1 % m]
            for r in rs[:2]:
                out.append(("meta", m, k, r, N))
    out.sort(key=lambda sp: (0 if sp[-1] >= N_RECORD_BEAT else 1, sp[-1]))
    return out[:MAX_SPECS]


# ------------------------------------------------------------------------ Haar graph and cost

def _nbr(MT, inv, N, S):
    """Neighbour array of size 2N x DEG. A-vertex g is g, B-vertex h is N+h.
    A(g) ~ B(s*g) gives B-index MT[s, g]; B(h) ~ A(s^-1 * h) gives A-index MT[inv[s], h]."""
    invS = inv[S]
    a = MT[S, :].T.astype(np.int64) + N
    b = MT[invS, :].T.astype(np.int64)
    return np.vstack([a, b])


def _cost(nbr, N):
    """Vertices not reached within DIAM steps from A(e) and from B(e). Zero means diameter <= DIAM."""
    n = 2 * N
    total = 0
    for src in (0, N):
        seen = np.zeros(n, dtype=bool)
        seen[src] = True
        fr = np.array([src], dtype=np.int64)
        for _ in range(DIAM):
            nx = nbr[fr].ravel()
            nx = nx[~seen[nx]]
            if nx.size == 0:
                break
            nx = np.unique(nx)
            seen[nx] = True
            fr = nx
        total += n - int(np.count_nonzero(seen))
    return total


def _anneal(st, deadline, rng):
    """Anneal the connection set of state st until cost 0 (returns True) or the deadline (returns False)."""
    MT, inv, N = st["MT"], st["inv"], st["N"]
    while time.monotonic() < deadline:
        if st["S"] is None:
            S = rng.choice(N, size=DEG, replace=False).astype(np.int64)
            st["S"] = S
            st["cur"] = _cost(_nbr(MT, inv, N, S), N)
            st["stall"] = 0
        if st["cur"] == 0:
            return True
        S, cur = st["S"], st["cur"]
        for _ in range(100):
            pos = int(rng.integers(DEG))
            x = int(rng.integers(N))
            if x in S:
                continue
            newS = S.copy()
            newS[pos] = x
            c = _cost(_nbr(MT, inv, N, newS), N)
            delta = c - cur
            if delta <= 0 or rng.random() < math.exp(-delta / TEMP):
                S, cur = newS, c
                st["stall"] = 0 if delta < 0 else st["stall"] + 1
            else:
                st["stall"] += 1
            if cur == 0:
                break
        st["S"], st["cur"] = S, cur
        if cur == 0:
            return True
        if st["stall"] >= STALL:
            st["S"] = None
    return False


def _haar_edges(MT, S, N):
    """Edges of the Haar graph: A(g) = g, B(h) = N+h, (g, A) ~ (s*g, B)."""
    edges = []
    for s in S:
        row = MT[int(s)].tolist()
        edges.extend((g, N + row[g]) for g in range(N))
    return 2 * N, edges


# --------------------------------------------------------------------------- fallbacks

def trivial(d, D):
    """Always-valid small graph for any (d, D)."""
    cands = []
    try:
        if D == 3 and d >= 3 and lib.is_prime_power(d - 1) and d - 1 <= 8:
            cands.append(lib.projective_plane_incidence(d - 1))
    except Exception:
        pass
    if D >= 2 and d >= 1:
        cands.append((2 * d, [(i, d + j) for i in range(d) for j in range(d)]))  # K_{d,d}
    cands.append((2, [(0, 1)]) if d >= 1 and D >= 1 else (1, []))
    for n, e in cands:
        try:
            if lib.is_valid(n, e, d, D):
                return n, e
        except Exception:
            pass
    return 1, []


def _fallback(d, D):
    """Valid order-660 Haar graph for d=6, D=5 (checked), else a trivial graph."""
    try:
        MT, _ = meta_table(33, 10, 26)
        n, edges = _haar_edges(MT, [0, 179, 116, 180, 47, 306], MT.shape[0])
        if lib.is_valid(n, edges, d, D):
            return n, edges
    except Exception:
        pass
    return trivial(d, D)


# ------------------------------------------------------------------------------- build

def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return trivial(d, D)
    t0 = time.monotonic()
    budget = max(3.0, min(0.8 * time_limit, time_limit - 10.0))
    deadline = t0 + budget
    rng = np.random.default_rng(seed)
    best = None
    try:
        states = [{"spec": sp, "N": sp[-1], "MT": None, "inv": None, "S": None,
                   "cur": None, "stall": 0, "dead": False} for sp in _specs()]
        while time.monotonic() < deadline:
            best_N = best[0] // 2 if best is not None else 0
            live = [s for s in states if not s["dead"] and s["N"] > best_N]
            if not live:
                break
            for st in live:
                now = time.monotonic()
                if now >= deadline:
                    break
                if st["MT"] is None:
                    try:
                        st["MT"], st["inv"] = _make(st["spec"])
                    except Exception:
                        st["dead"] = True
                        continue
                if st["N"] <= (best[0] // 2 if best is not None else 0):
                    continue
                ok = _anneal(st, min(deadline, now + SLICE), rng)
                if ok:
                    try:
                        n, edges = _haar_edges(st["MT"], st["S"], st["N"])
                        if lib.is_valid(n, edges, DEG, DIAM) and (best is None or n > best[0]):
                            best = (n, edges)
                    except Exception:
                        pass
                    st["S"], st["cur"] = None, None
    except Exception:
        pass
    if best is not None:
        return best
    return _fallback(d, D)
