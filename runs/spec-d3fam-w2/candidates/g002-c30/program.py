import math
import random
import time

import lib


# ---------------------------------------------------------------------------
# Difference-cover search on bipartite group lifts.
#
# Two base vertices a, b with darts (a, b, s) for s in S give the bipartite
# graph on G x {0,1} with a_x ~ b_{x s}. Same-side pairs are at distance 2
# exactly when S S^{-1} = G, and then every cross pair is within distance 3.
# So a set S of size d with S S^{-1} = G gives a valid graph of order 2|G|.
# Left-translating S preserves the covering property, so we may take 0 in S
# (0 is the identity in both cyclic and semidirect codings).
# ---------------------------------------------------------------------------

def _apply(cnt, S, i, v, sign, R):
    """Add (sign > 0) or remove (sign < 0) all ordered-pair contributions of value v at slot i.

    Contributions are R[v][v], R[v][S_j] and R[S_j][v] for j != i. Returns the change in the
    number of uncovered group elements (cnt entries equal to zero).
    """
    row = R[v]
    targets = [row[v]]
    for j, b in enumerate(S):
        if j != i:
            targets.append(row[b])
            targets.append(R[b][v])
    ch = 0
    if sign > 0:
        for g in targets:
            if cnt[g] == 0:
                ch -= 1
            cnt[g] += 1
    else:
        for g in targets:
            cnt[g] -= 1
            if cnt[g] == 0:
                ch += 1
    return ch


def _new_job(N, mul, inv):
    return {"N": N, "mul": mul, "inv": inv, "R": None, "S": None,
            "cnt": None, "unc": None, "steps": 0, "dead": False}


def _init_job(job, d, rng):
    N, mul, inv = job["N"], job["mul"], job["inv"]
    iv = [inv(y) for y in range(N)]
    R = [[mul(x, iv[y]) for y in range(N)] for x in range(N)]
    S = [0] + rng.sample(range(1, N), d - 1)
    cnt = [0] * N
    for a in S:
        for b in S:
            cnt[R[a][b]] += 1
    job["R"] = R
    job["S"] = S
    job["cnt"] = cnt
    job["unc"] = sum(1 for c in cnt if c == 0)


def _run(job, steps, d, rng):
    """Advance the annealing of one job by a fixed number of moves."""
    S, cnt, R, N = job["S"], job["cnt"], job["R"], job["N"]
    unc, t = job["unc"], job["steps"]
    for _ in range(steps):
        if unc == 0:
            break
        i = rng.randrange(1, d)
        x = rng.randrange(1, N)
        if x in S:
            continue
        old = S[i]
        frac = (t % 20000) / 20000.0
        T = 0.6 * (0.03 ** frac)
        delta = _apply(cnt, S, i, old, -1, R) + _apply(cnt, S, i, x, +1, R)
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            S[i] = x
            unc += delta
        else:
            _apply(cnt, S, i, x, -1, R)
            _apply(cnt, S, i, old, +1, R)
        t += 1
    job["unc"] = unc
    job["steps"] = t


def _groups(N, rng):
    """Cyclic group of order N plus up to two random semidirect products Z_m x| Z_k."""
    out = [lib.cyclic_group(N)]
    cand = []
    for k in range(2, N + 1):
        if N % k:
            continue
        m = N // k
        if m < 2:
            continue
        for r in range(1, m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                cand.append((m, k, r))
    rng.shuffle(cand)
    for m, k, r in cand[:2]:
        try:
            out.append(lib.semidirect_group(m, k, r))
        except ValueError:
            pass
    return out


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ---------------------------------------------------------------- driver

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(1.0, 0.85 * time_limit - 5.0)
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    best = lib.haar_graph(d, range(d))   # K_{d,d}, diameter 2

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D == 2 or d < 3:
        return best

    # Moore-extremal case: incidence graph of PG(2, d-1) is optimal.
    if lib.is_prime_power(d - 1):
        try:
            consider(*lib.projective_plane_incidence(d - 1))
        except Exception:
            pass
        return best

    # Known record family for d = q + 2, q a prime power.
    if d - 2 >= 3 and lib.is_prime_power(d - 2):
        try:
            consider(*lib.araujo_lopez_graph(d - 2))
        except Exception:
            pass

    pg = _best_pg(d)
    if pg is not None:
        consider(pg[0], pg[1])

    # Search for difference covers of size d in groups of order N, 2N > best.
    lo = best[0] // 2 + 1
    hi = d * (d - 1) + 1
    if lo > hi:
        return best

    jobs = []
    for N in range(hi, lo - 1, -1):
        if N < d:
            continue
        for _o, mul, inv in _groups(N, rng):
            jobs.append(_new_job(N, mul, inv))

    chunk = 400
    while time.monotonic() < deadline:
        live = [j for j in jobs if not j["dead"] and 2 * j["N"] > best[0]]
        if not live:
            break
        for job in live:
            if time.monotonic() >= deadline:
                break
            if job["R"] is None:
                _init_job(job, d, rng)
            _run(job, chunk, d, rng)
            if job["unc"] == 0:
                S = job["S"]
                n, e = lib.group_lift(2, [(0, 1, g) for g in S], job["N"], job["mul"])
                if n > best[0] and lib.is_valid(n, e, d, D):
                    best = (n, e)
                else:
                    job["dead"] = True
        chunk = min(chunk * 2, 4000)

    return best
