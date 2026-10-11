import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: bi-Cayley (Haar-type) search for diameter 3.
#
# For a group G of order G (cyclic or semidirect Z_m x| Z_k) and a connection
# set S of d distinct elements, the graph has vertices a_x, b_y (x, y in G) and
# edges a_x -- b_{x s} for s in S. Left translation is an automorphism, so the
# graph has diameter <= 3 iff every vertex is within distance 3 of a_e and of b_e.
# Cost = number of vertices unreached from a_e plus from b_e (0 means valid).
# Several groups are searched round-robin with Metropolis moves on S; the largest
# group order that reaches cost 0 is printed. Output is "n m" plus edges.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXG 512
#define MAXD 64
#define MAXJ 400
#define STEPS 800
#define STALE 30000
#define TEMP 0.5

static int G, dd, MM, KK;
static int pw[MAXG];
static int mulT[MAXG][MAXG];
static int invT[MAXG];

static uint64_t rs = 0x9E3779B97F4A7C15ULL;
static uint64_t rnd64(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rint_(int k) { return (int)(rnd64() % (uint64_t)k); }
static double rdbl(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

typedef struct {
    int m, k, r, G;
    int active;
    int init;
    int S[MAXD];
    unsigned char inS[MAXG];
    int cost;
    int runbest;
    long stale;
} Job;

static Job jobs[MAXJ];
static int njobs;
static clock_t t0;
static double tl;

static double elapsed(void) { return (double)(clock() - t0) / CLOCKS_PER_SEC; }

static void set_group(int m, int k, int r) {
    MM = m; KK = k; G = m * k;
    int p = 1 % m;
    for (int b = 0; b < k; b++) { pw[b] = p; p = (int)(((long)p * r) % m); }
    for (int x = 0; x < G; x++) {
        int a = x / k, b = x % k;
        for (int y = 0; y < G; y++) {
            int c = y / k, e = y % k;
            mulT[x][y] = ((a + (int)(((long)pw[b] * c) % m)) % m) * k + (b + e) % k;
        }
    }
    for (int x = 0; x < G; x++) {
        invT[x] = 0;
        for (int y = 0; y < G; y++) if (mulT[x][y] == 0) { invT[x] = y; break; }
    }
}

static int visS[2 * MAXG];
static int stampc = 0;
static int qb[2 * MAXG];

/* Number of vertices reached from src within 3 steps. */
static int reach(const int *S, int src) {
    stampc++;
    int qt = 0;
    qb[qt++] = src;
    visS[src] = stampc;
    int fs = 0, fe = 1;
    for (int depth = 0; depth < 3; depth++) {
        for (int i = fs; i < fe; i++) {
            int u = qb[i];
            if (u < G) {
                for (int j = 0; j < dd; j++) {
                    int v = G + mulT[u][S[j]];
                    if (visS[v] != stampc) { visS[v] = stampc; qb[qt++] = v; }
                }
            } else {
                int y = u - G;
                for (int j = 0; j < dd; j++) {
                    int v = mulT[y][invT[S[j]]];
                    if (visS[v] != stampc) { visS[v] = stampc; qb[qt++] = v; }
                }
            }
        }
        fs = fe; fe = qt;
    }
    return qt;
}

static int cost_of(const int *S) {
    int n2 = 2 * G;
    return (n2 - reach(S, 0)) + (n2 - reach(S, G));
}

static void job_reinit(Job *J) {
    memset(J->inS, 0, sizeof(J->inS));
    for (int j = 0; j < dd; j++) {
        int x;
        do { x = rint_(G); } while (J->inS[x]);
        J->inS[x] = 1;
        J->S[j] = x;
    }
    J->cost = cost_of(J->S);
    J->runbest = J->cost;
    J->stale = 0;
}

/* Run up to STEPS Metropolis moves on the current job (its group must be set). */
static void job_steps(Job *J, int *found) {
    for (int s = 0; s < STEPS; s++) {
        if (J->cost == 0) { *found = 1; return; }
        int i = rint_(dd);
        int x;
        do { x = rint_(G); } while (J->inS[x]);
        int old = J->S[i];
        J->S[i] = x;
        J->inS[old] = 0;
        J->inS[x] = 1;
        int nc = cost_of(J->S);
        int delta = nc - J->cost;
        if (delta <= 0 || rdbl() < exp(-(double)delta / TEMP)) {
            J->cost = nc;
            if (nc < J->runbest) { J->runbest = nc; J->stale = 0; }
            else J->stale++;
        } else {
            J->S[i] = old;
            J->inS[x] = 0;
            J->inS[old] = 1;
            J->stale++;
        }
        if (J->cost == 0) { *found = 1; return; }
        if (J->stale > STALE) job_reinit(J);
    }
}

int main(int argc, char **argv) {
    if (argc < 5) { printf("0 0\n"); return 0; }
    dd = atoi(argv[1]);
    int D = atoi(argv[2]);
    uint64_t seed = (uint64_t)strtoull(argv[3], NULL, 10);
    rs ^= seed * 0xBF58476D1CE4E5B9ULL + 0x1234567ULL;
    if (rs == 0) rs = 1;
    tl = atof(argv[4]);
    t0 = clock();
    if (D != 3 || dd < 2 || dd > MAXD) { printf("0 0\n"); return 0; }

    njobs = 0;
    for (int a = 5; a + 2 < argc && njobs < MAXJ; a += 3) {
        int m = atoi(argv[a]), k = atoi(argv[a + 1]), r = atoi(argv[a + 2]);
        Job *J = &jobs[njobs++];
        J->m = m; J->k = k; J->r = r;
        J->G = m * k;
        J->init = 0;
        J->active = (m >= 2 && k >= 1 && m * k <= MAXG && m * k > dd && r >= 1 && r < m);
    }

    int bestG = 0, bestIdx = -1;
    int bestS[MAXD];

    for (;;) {
        int any = 0;
        for (int j = 0; j < njobs; j++) {
            Job *J = &jobs[j];
            if (!J->active) continue;
            if (J->G <= bestG) { J->active = 0; continue; }
            if (elapsed() > tl) goto done;
            any = 1;
            set_group(J->m, J->k, J->r);
            if (!J->init) { job_reinit(J); J->init = 1; }
            int found = 0;
            job_steps(J, &found);
            if (found) {
                bestG = J->G;
                bestIdx = j;
                memcpy(bestS, J->S, sizeof(int) * (size_t)dd);
                J->active = 0;
            }
        }
        if (!any) break;
        if (elapsed() > tl) break;
    }

done:
    if (bestIdx < 0) { printf("0 0\n"); return 0; }
    {
        Job *B = &jobs[bestIdx];
        set_group(B->m, B->k, B->r);
        int n2 = 2 * G;
        int me = G * dd;
        printf("%d %d\n", n2, me);
        for (int j = 0; j < dd; j++)
            for (int x = 0; x < G; x++)
                printf("%d %d\n", x, G + mulT[x][bestS[j]]);
    }
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3).
# ----------------------------------------------------------------------------

def _pg_data(q):
    """Return (m, edges, point_lines, line_points, index, pts) for PG(2, q)."""
    pts = lib.projective_points(q)
    n2, edges = lib.projective_plane_incidence(q)
    m = n2 // 2
    point_lines = [[] for _ in range(m)]
    line_points = [[] for _ in range(m)]
    for u, v in edges:
        point_lines[u].append(v - m)
        line_points[v - m].append(u)
    index = {p: i for i, p in enumerate(pts)}
    return m, edges, point_lines, line_points, index, pts


def _loads_ok(S, s, m, point_lines, line_points):
    """True if every line holds <= s points of S and every point lies on <= s lines indexed by S."""
    cl = [0] * m
    cp = [0] * m
    for P in S:
        for L in point_lines[P]:
            cl[L] += 1
        for Q in line_points[P]:
            cp[Q] += 1
    return max(cl, default=0) <= s and max(cp, default=0) <= s


def _greedy_arc(m, s, point_lines, line_points, rng, trials, deadline):
    """Randomized greedy choice of S with all loads <= s; returns the largest found."""
    best = []
    order = list(range(m))
    for _ in range(trials):
        if time.monotonic() > deadline:
            break
        rng.shuffle(order)
        cl = [0] * m
        cp = [0] * m
        S = []
        for P in order:
            if all(cl[L] < s for L in point_lines[P]) and all(cp[Q] < s for Q in line_points[P]):
                S.append(P)
                for L in point_lines[P]:
                    cl[L] += 1
                for Q in line_points[P]:
                    cp[Q] += 1
        if len(S) > len(best):
            best = S
    return best


def _conic_set(q, index, F):
    """Conic (plus nucleus for even q) as a point-index set."""
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _arc_graph(m, edges, point_lines, line_points, S):
    """Old PG incidence plus a new A and a new B vertex per element of S."""
    k = len(S)
    n = 2 * m + 2 * k
    E = list(edges)
    for t, P in enumerate(S):
        x = 2 * m + t
        for L in point_lines[P]:
            E.append((x, m + L))
    for t, j in enumerate(S):
        b = 2 * m + k + t
        for Q in line_points[j]:
            E.append((Q, b))
    return n, E


def _arc_extensions(d, deadline, rng):
    """Return (n, edges) candidates for each prime power q with q + 1 <= d."""
    out = []
    for q in range(2, min(d - 1, 23) + 1):
        if not lib.is_prime_power(q):
            continue
        if time.monotonic() > deadline:
            break
        s = d - q - 1
        m, edges, point_lines, line_points, index, pts = _pg_data(q)
        cands = []
        if s >= 1:
            cands.append(_greedy_arc(m, s, point_lines, line_points, rng, 40, deadline))
        if s >= 2:
            F = lib.GF(q)
            cs = _conic_set(q, index, F)
            if _loads_ok(cs, s, m, point_lines, line_points):
                cands.append(cs)
        S = max(cands, key=len, default=[])
        if not _loads_ok(S, s, m, point_lines, line_points):
            continue
        out.append(_arc_graph(m, edges, point_lines, line_points, S))
    return out


# ----------------------------------------------------------------------------
# Bi-Cayley (Haar-type) job list for the C engine (diameter 3).
# ----------------------------------------------------------------------------

def _haar_jobs(d, Gmin, Gmax, rng, per_G=3, cap=150):
    """(m, k, r) group descriptions, largest order first; semidirect Z_m x| Z_k with r^k = 1 mod m."""
    jobs = []
    for G in range(Gmax, Gmin - 1, -1):
        if G <= d:
            break
        cand = [(G, 1, 1)]          # cyclic group Z_G
        extra = []
        for k in range(2, 13):
            if G % k:
                continue
            m = G // k
            if m < 2:
                continue
            rs = [r for r in range(1, m) if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m]
            if not rs:
                continue
            if 1 in rs:
                extra.append((m, k, 1))             # direct product Z_m x Z_k
            others = [r for r in rs if r != 1]
            if others:
                extra.append((m, k, rng.choice(others)))
        rng.shuffle(extra)
        cand += extra
        jobs += cand[:per_G]
        if len(jobs) >= cap:
            break
    return jobs[:cap]


# ----------------------------------------------------------------------------
# Generalized quadrangle W(q) (diameter 4), used for D >= 4.
# ----------------------------------------------------------------------------

def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q); diameter 4."""
    F = lib.GF(q)
    pts = [v for v in itertools.product(range(q), repeat=4)
           if any(v) and next(c for c in v if c) == 1]
    index = {v: i for i, v in enumerate(pts)}
    P = len(pts)

    def norm(v):
        c = next(x for x in v if x)
        inv = F.inv(c)
        return tuple(F.mul(inv, x) for x in v)

    def form(x, y):
        t = F.sub(F.mul(x[0], y[1]), F.mul(x[1], y[0]))
        return F.add(t, F.sub(F.mul(x[2], y[3]), F.mul(x[3], y[2])))

    covered = set()
    lines = []
    for i in range(P):
        x = pts[i]
        for j in range(i + 1, P):
            if (i, j) in covered:
                continue
            y = pts[j]
            if form(x, y) != 0:
                continue
            L = set()
            for a in range(q):
                for b in range(q):
                    if a == 0 and b == 0:
                        continue
                    v = tuple(F.add(F.mul(a, x[k]), F.mul(b, y[k])) for k in range(4))
                    if any(v):
                        L.add(index[norm(v)])
            L = sorted(L)
            lines.append(L)
            for p in L:
                for r in L:
                    if p < r:
                        covered.add((p, r))

    edges = []
    for j, L in enumerate(lines):
        for p in L:
            edges.append((p, P + j))
    return 2 * P, edges


def _best_gq(d):
    """W(q) for the largest prime power q with q + 1 <= d, restricted to small q for speed."""
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Simulated annealing over voltage lifts (used for D >= 4, unchanged).
# ----------------------------------------------------------------------------

_BIG = 10 ** 9


def _sample_group(G, rng):
    """Return (order, mul) for a random semidirect product Z_m x| Z_k2 of order G, or None."""
    for _ in range(80):
        k2 = rng.choice([1, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12])
        if G % k2:
            continue
        m = G // k2
        if m < 2:
            continue
        if k2 == 1:
            r = 1
        else:
            cands = [r for r in rng.sample(range(1, m), min(m - 1, 60))
                     if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m]
            if not cands:
                continue
            r = rng.choice(cands)
        try:
            order, mul, _ = lib.semidirect_group(m, k2, r)
        except ValueError:
            continue
        return order, mul
    return None


def _right_perm(mul, G, s):
    """Permutation g -> mul(g, s) of the group."""
    return [mul(g, s) for g in range(G)]


def _cost(k, G, D, darts, perms):
    """Number of (representative, vertex) pairs not reached within distance D. Zero means valid."""
    if len({(i, j, s) for i, j, s in darts}) < len(darts):
        return _BIG
    N = 2 * k * G
    adj = [[] for _ in range(N)]
    for (i, j, _s), pm in zip(darts, perms):
        base_a = i * G
        base_b = (k + j) * G
        for g in range(G):
            a = base_a + g
            b = base_b + pm[g]
            adj[a].append(b)
            adj[b].append(a)
    reps = [i * G for i in range(k)] + [(k + j) * G for j in range(k)]
    total = 0
    for src in reps:
        seen = [False] * N
        seen[src] = True
        frontier = [src]
        count = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                for v in adj[u]:
                    if not seen[v]:
                        seen[v] = True
                        nxt.append(v)
            count += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += N - count
    return total


def _edges(k, G, darts, perms):
    E = set()
    for (i, j, _s), pm in zip(darts, perms):
        for g in range(G):
            E.add((i * G + g, (k + j) * G + pm[g]))
    return 2 * k * G, sorted(E)


def _anneal(d, D, k, G, mul, rng, deadline, iters):
    """Simulated annealing over voltages and per-layer B-assignments."""
    darts = []
    for _ in range(d):
        p = rng.sample(range(k), k)
        for i in range(k):
            darts.append([i, p[i], rng.randrange(G)])
    perms = [_right_perm(mul, G, s) for _, _, s in darts]
    cost = _cost(k, G, D, darts, perms)

    T = 1.0
    for _ in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        T = max(0.05, T * 0.997)

        if rng.random() < 0.7 or k == 1:
            idx = rng.randrange(len(darts))
            old_s = darts[idx][2]
            new_s = rng.randrange(G)
            if new_s == old_s:
                continue
            old_perm = perms[idx]
            darts[idx][2] = new_s
            perms[idx] = _right_perm(mul, G, new_s)
            c2 = _cost(k, G, D, darts, perms)
            delta = c2 - cost
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                cost = c2
            else:
                darts[idx][2] = old_s
                perms[idx] = old_perm
        else:
            L = rng.randrange(d)
            a, b = rng.sample(range(k), 2)
            ia, ib = L * k + a, L * k + b
            darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
            c2 = _cost(k, G, D, darts, perms)
            delta = c2 - cost
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                cost = c2
            else:
                darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]

    if cost == 0:
        return _edges(k, G, darts, perms)
    return None


# ----------------------------------------------------------------------------
# Build
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t_start = time.monotonic()
    end = t_start + 0.85 * time_limit - 1.0
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))

    def consider(g):
        nonlocal best
        if g[0] > best[0] and lib.is_valid(g[0], g[1], d, D):
            best = (g[0], g[1])

    # Arc-extended projective plane graphs (valid for D >= 3).
    if D >= 3 and time.monotonic() < end:
        cands = _arc_extensions(d, end, random.Random(seed * 7919 + d))
        for g in sorted(cands, key=lambda t: -t[0]):
            consider(g)

    # Bold change for D = 3: bi-Cayley (Haar-type) graphs over cyclic and
    # semidirect groups, searched by annealing the connection set S.
    # A graph of order 2|G| with |G| > best/2 is sought.
    if D == 3:
        Gmax = lib.moore_bound(d, D) // 2
        Gmin = max(d + 1, best[0] // 2 + 1)
        if Gmin <= Gmax and time.monotonic() < end:
            jobs = _haar_jobs(d, Gmin, Gmax, rng)
            cbudget = end - time.monotonic()
            if jobs and cbudget > 6.0:
                flat = []
                for m, k, r in jobs:
                    flat += [m, k, r]
                try:
                    out = lib.run_c(C_SOURCE, [d, D, seed, round(cbudget - 3.0, 2)] + flat,
                                    timeout=cbudget + 5)
                    consider(lib.parse_graph_text(out))
                except Exception:
                    pass

    # Voltage-lift annealing for D >= 4 (unchanged from parent).
    if D >= 4:
        # Fast construction for D >= 4.
        gq = _best_gq(d)
        if gq is not None:
            consider(gq)
        ks = [1, 2, 2, 3, 4] if D >= 5 else [1, 1, 2, 3]
        while time.monotonic() < end:
            k = rng.choice(ks)
            base = best[0] // (2 * k)
            G = max(2, base + 1 + rng.randrange(0, max(3, base // 8 + 1)))
            g = _sample_group(G, rng)
            if g is None:
                continue
            order, mul = g
            res = _anneal(d, D, k, order, mul, rng, end, iters=400)
            if res is not None:
                consider(res)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best[0], list(best[1])
