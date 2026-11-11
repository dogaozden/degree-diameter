"""Bi-Cayley search over explicit finite groups, with the metacyclic parent as fallback.

New construction: a bipartite graph on G x {0,1} with edges (g,0)-(g s,1) for s in S, where G is a
finite group and S is a set of d distinct elements. Left multiplication is an automorphism that acts
regularly on each side, so the diameter is at most D iff BFS from (1,0) and (1,1) reaches everything
within D. The C engine stores the group as a full multiplication table and anneals S against the exact
unreached-pair count. Group families:
  kind 0: PGL(2,p), kind 1: PSL(2,p), kind 2: SL(2,p), kind 3: metacyclic Z_m x|_r Z_k.
PGL(2,11) has order 1320 (graph order 2640, above the 2184 record). PSL(2,13) gives exactly 2184.

Schedule: the best known algebraic start is the initial fallback. Phase 1 climbs with short slices
over small non-abelian and metacyclic candidates. Phase 2 spends the remaining time round-robin on the
largest algebraic groups plus a metacyclic group at order best/2 + 1, which keeps the parent's
record-targeted behaviour. Every returned graph is checked with lib.is_valid, and only strictly
larger valid graphs are accepted.
"""
import itertools
import math
import random
import time

import lib

MAXG = 2500
MAXD = 16

C_SOURCE = r'''
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXG 2500
#define MAXD 16

static int d, D, N, ID, P, KIND;
static int MT[MAXG * MAXG];
static int INV[MAXG];
static int ELEM[MAXG][4];
static int IDX[17 * 17 * 17 * 17];
static int INVP[17];
static int S[MAXD], SI[MAXD];
static int vis[2 * MAXG];
static int qu[2 * MAXG];
static int stampc = 0;

static uint64_t rs = 88172645463325252ULL;
static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double rnd01(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

static int canon_id(int a, int b, int c, int dd) {
    int m[4] = {a, b, c, dd};
    if (KIND != 2) {
        for (int i = 0; i < 4; i++) {
            if (m[i]) {
                int iv = INVP[m[i]];
                for (int j = 0; j < 4; j++) m[j] = m[j] * iv % P;
                break;
            }
        }
    }
    int code = ((m[0] * P + m[1]) * P + m[2]) * P + m[3];
    return IDX[code];
}

static int mat_mul_id(int x, int y) {
    const int *A = ELEM[x], *B = ELEM[y];
    int a = (A[0] * B[0] + A[1] * B[2]) % P;
    int b = (A[0] * B[1] + A[1] * B[3]) % P;
    int c = (A[2] * B[0] + A[3] * B[2]) % P;
    int dd = (A[2] * B[1] + A[3] * B[3]) % P;
    return canon_id(a, b, c, dd);
}

static int is_square_mod(int v) {
    for (int x = 0; x < P; x++)
        if ((x * x) % P == v) return 1;
    return 0;
}

static void fill_inverses(void) {
    for (int i = 0; i < N; i++) {
        INV[i] = -1;
        for (int j = 0; j < N; j++) {
            if (MT[i * N + j] == ID) { INV[i] = j; break; }
        }
    }
}

static int build_matrix_group(int p, int kind) {
    P = p;
    KIND = kind;
    for (int x = 1; x < p; x++)
        for (int y = 1; y < p; y++)
            if (x * y % p == 1) INVP[x] = y;
    int psz = p * p * p * p;
    for (int i = 0; i < psz; i++) IDX[i] = -1;
    N = 0;
    for (int a = 0; a < p; a++)
    for (int b = 0; b < p; b++)
    for (int c = 0; c < p; c++)
    for (int e = 0; e < p; e++) {
        int det = ((a * e - b * c) % p + p) % p;
        if (det == 0) continue;
        if (kind == 2) {
            if (det != 1) continue;
        } else {
            int m[4] = {a, b, c, e};
            int first = 0;
            for (int i = 0; i < 4; i++) if (m[i]) { first = m[i]; break; }
            if (first != 1) continue;
            if (kind == 1 && !is_square_mod(det)) continue;
        }
        if (N >= MAXG) return 0;
        ELEM[N][0] = a; ELEM[N][1] = b; ELEM[N][2] = c; ELEM[N][3] = e;
        IDX[((a * p + b) * p + c) * p + e] = N;
        N++;
    }
    ID = canon_id(1, 0, 0, 1);
    if (ID < 0) return 0;
    for (int i = 0; i < N; i++)
        for (int j = 0; j < N; j++) {
            int t = mat_mul_id(i, j);
            if (t < 0) return 0;
            MT[i * N + j] = t;
        }
    fill_inverses();
    for (int i = 0; i < N; i++) if (INV[i] < 0) return 0;
    return 1;
}

/* Metacyclic group Z_m x|_r Z_k, element a*k+b, (a,b)(c,e) = (a + r^b c, b + e). */
static int build_meta(int m, int k, int r) {
    if (m < 1 || k < 1) return 0;
    long nn = (long)m * k;
    if (nn > MAXG) return 0;
    N = (int)nn;
    ID = 0;
    static int rp[MAXG];
    rp[0] = 1 % m;
    for (int b = 1; b < k; b++) rp[b] = (int)((long)rp[b - 1] * r % m);
    for (int u = 0; u < N; u++) {
        int a = u / k, b = u % k;
        for (int w = 0; w < N; w++) {
            int c = w / k, e = w % k;
            long v = (a + (long)rp[b] * c) % m;
            MT[u * N + w] = (int)(v * k + (b + e) % k);
        }
    }
    fill_inverses();
    for (int i = 0; i < N; i++) if (INV[i] < 0) return 0;
    return 1;
}

/* Sum over the two side-identities of unreached vertices within D (0 iff diameter <= D). */
static long eval_bad(void) {
    long total = 0;
    int NN = N;
    for (int src = 0; src < 2; src++) {
        int s0 = src * NN + ID;
        stampc++;
        int head = 0, tail = 0;
        qu[tail++] = s0;
        vis[s0] = stampc;
        for (int dep = 0; dep < D && head < tail; dep++) {
            int lim = tail;
            while (head < lim) {
                int v = qu[head++];
                if (v < NN) {
                    const int *row = MT + (size_t)v * NN;
                    for (int i = 0; i < d; i++) {
                        int u = NN + row[S[i]];
                        if (vis[u] != stampc) { vis[u] = stampc; qu[tail++] = u; }
                    }
                } else {
                    const int *row = MT + (size_t)(v - NN) * NN;
                    for (int i = 0; i < d; i++) {
                        int u = row[SI[i]];
                        if (vis[u] != stampc) { vis[u] = stampc; qu[tail++] = u; }
                    }
                }
            }
        }
        total += 2L * NN - tail;
    }
    return total;
}

static int in_S(int x, int upto) {
    for (int i = 0; i < upto; i++) if (S[i] == x) return 1;
    return 0;
}

static int search(double until) {
    const int MAXIT = 40000;
    while (now() < until) {
        for (int i = 0; i < d; i++) {
            int x;
            do { x = rndint(N); } while (in_S(x, i));
            S[i] = x;
            SI[i] = INV[x];
        }
        long bad = eval_bad();
        double T = 1.0;
        for (int it = 0; it < MAXIT && bad > 0; it++) {
            if ((it & 127) == 0 && now() > until) return 0;
            int i = rndint(d);
            int ng = rndint(N);
            if (in_S(ng, d)) continue;
            int old = S[i];
            S[i] = ng;
            SI[i] = INV[ng];
            long nb = eval_bad();
            if (nb <= bad || rnd01() < exp((double)(bad - nb) / T)) {
                bad = nb;
            } else {
                S[i] = old;
                SI[i] = INV[old];
            }
            T *= 0.9997;
            if (T < 0.03) T = 1.0;
        }
        if (bad == 0) return 1;
    }
    return 0;
}

static void print_result(void) {
    printf("%d %d\n", 2 * N, N * d);
    for (int g = 0; g < N; g++)
        for (int i = 0; i < d; i++)
            printf("%d %d\n", g, N + MT[g * N + S[i]]);
}

int main(int argc, char **argv) {
    if (argc < 9) { printf("0 0\n"); return 0; }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double tl = atof(argv[4]);
    int kind = atoi(argv[5]);
    int x = atoi(argv[6]);
    int y = atoi(argv[7]);
    int z = atoi(argv[8]);
    if (d < 1 || d > MAXD || D < 1) { printf("0 0\n"); return 0; }
    int ok;
    if (kind <= 2) {
        if (x < 2 || x > 17) { printf("0 0\n"); return 0; }
        ok = build_matrix_group(x, kind);
    } else {
        ok = build_meta(x, y, z);
    }
    if (!ok || N < d + 1) { printf("0 0\n"); return 0; }
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();
    double t_end = now() + tl * 0.9;
    if (search(t_end)) print_result();
    else printf("0 0\n");
    return 0;
}
'''


def _gq_w(q):
    """Incidence graph of points and lines of W(q): degree q+1, diameter 4."""
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


def _largest_prime_power_le(x):
    for q in range(x, 1, -1):
        if lib.is_prime_power(q):
            return q
    return None


def known_starts(d, D):
    """Algebraic candidates valid for diameter D (may be empty)."""
    out = []
    if D >= 3 and d - 1 >= 2 and lib.is_prime_power(d - 1):
        out.append(lib.projective_plane_incidence(d - 1))
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        out.append(lib.araujo_lopez_graph(d - 2))
    if D >= 4:
        q = _largest_prime_power_le(min(d - 1, 9))
        if q is not None and q >= 2:
            out.append(_gq_w(q))
    return out


def _alg_groups():
    """(order, kind, p) for PGL(2,p), PSL(2,p), SL(2,p), p prime."""
    out = []
    for p in (3, 5, 7, 11, 13, 17):
        n = p * (p * p - 1)
        out.append((n, 0, p))
        out.append((n // 2, 1, p))
        out.append((n, 2, p))
    return out


ALG = _alg_groups()


def _meta_choices(N):
    """All (m, k, r) giving metacyclic Z_m x|_r Z_k of order N (r = 1 always present)."""
    out = []
    for m in range(1, N + 1):
        if N % m:
            continue
        k = N // m
        if m == 1:
            out.append((1, N, 0))
            continue
        for r in range(1, m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    return out


def _pick_meta(N, rng):
    choices = _meta_choices(N)
    nonab = [c for c in choices if c[2] not in (0, 1)]
    pool = nonab if (nonab and rng.random() < 0.7) else choices
    return rng.choice(pool)


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]
    if d == 2:
        L = 2 * D
        return L, [(i, (i + 1) % L) for i in range(L)]

    best = lib.haar_graph(d, range(d))  # K_{d,d}: always valid for D >= 2
    for cand in known_starts(d, D):
        n, e = cand
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    moore = lib.moore_bound(d, D)
    if best[0] >= moore or d > MAXD or d + 1 > MAXG:
        return best

    deadline = t0 + 0.85 * time_limit - 1.5
    if deadline - time.monotonic() < 2.0:
        return best

    rng = random.Random(seed * 1000003 + d * 997 + D)
    box = {"best": best, "calls": 0, "errors": 0}

    def attempt(job, slice_s):
        box["calls"] += 1
        kind, x, y, z = job
        try:
            text = lib.run_c(C_SOURCE,
                             [d, D, seed * 1000 + box["calls"], f"{slice_s:.2f}", kind, x, y, z],
                             timeout=slice_s + 10)
            n, e = lib.parse_graph_text(text)
        except Exception:
            box["errors"] += 1
            return False
        box["errors"] = 0
        if n > box["best"][0] and lib.is_valid(n, e, d, D):
            box["best"] = (n, e)
            return True
        return False

    def alg_jobs(ascending):
        b = box["best"][0]
        ok = [(N, kind, p) for N, kind, p in ALG
              if d + 1 <= N <= MAXG and b < 2 * N <= moore]
        ok.sort(reverse=not ascending)
        return [(kind, p, 0, 0) for N, kind, p in ok]

    def meta_jobs():
        nm = box["best"][0] // 2 + 1
        if nm < d + 1 or nm > MAXG or 2 * nm > moore:
            return []
        m, k, r = _pick_meta(nm, rng)
        return [(3, m, k, r)]

    # Phase 1: quick climbing over small groups, short slices per job.
    phase1_end = time.monotonic() + 0.35 * (deadline - time.monotonic())
    while time.monotonic() < phase1_end - 0.3 and box["errors"] < 3:
        moved = False
        for job in alg_jobs(True) + meta_jobs():
            rem = phase1_end - time.monotonic()
            if rem < 0.3:
                break
            if attempt(job, min(1.0, rem)):
                moved = True
                break
        if not moved:
            break

    # Phase 2: round-robin over the largest algebraic groups and the metacyclic target order.
    while box["errors"] < 3:
        if deadline - time.monotonic() < 1.0:
            break
        jobs = alg_jobs(False)[:3] + meta_jobs()
        if not jobs:
            break
        moved = False
        for job in jobs:
            rem = deadline - time.monotonic()
            if rem < 1.0:
                break
            if attempt(job, min(8.0, rem)):
                moved = True
                break

    return box["best"]
