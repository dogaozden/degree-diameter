import math
import time

import lib


# ----------------------------------------------------------------------------
# Bold change: bi-regular voltage lifts over NON-metacyclic groups.
#
# The C engine takes a finite group chosen by Python:
#   type 0: semidirect Z_m x| Z_k (p1=m, p2=k, p3=r)
#   type 1: affine group AGL(1,p)        (p1=p)
#   type 2: projective special linear PSL(2,p)  (p1=p)
#   type 3: projective general linear PGL(2,p)  (p1=p)
# Group multiplication is tabulated in C. A lift over K base pairs with
# 2*K*|G| vertices is searched by simulated annealing on layer permutations
# and voltages (cost = unreached (block, vertex) pairs + duplicate penalty).
# Python climbs a ladder of candidate (group, K) pairs nearest a goal size,
# validates every candidate with lib.is_valid, and keeps K_{d,d} / PG(2,q)
# as fallbacks.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXK 4
#define MAXG 2600
#define PEN 1000
#define ITERS 20000
#define PAT 6000

static uint64_t rs;

static uint64_t rnd64(void) {
    uint64_t x = rs;
    x ^= x >> 12;
    x ^= x << 25;
    x ^= x >> 27;
    rs = x;
    return x * 2685821657736338717ULL;
}
static double rnd01(void) {
    return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0);
}
static int rndint(int n) {
    return (int)(rnd64() % (uint64_t)n);
}

static int DEG, DIAM, K, G, N, ID;
static int *MT, *INV;
static int *nbr, *lay, *vol;
static uint8_t *cur, *scr, *tmpb;
static uint8_t POP[256];
static uint8_t FULL;
static int timed_out;
static double tstart, TL;
static int64_t LASTCOST;

#define MUL(x, y) MT[(size_t)(x) * (size_t)G + (size_t)(y)]

static double now_s(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)ts.tv_sec + (double)ts.tv_nsec * 1e-9;
}
static double elapsed(void) {
    return now_s() - tstart;
}

static int64_t powmod(int64_t b, int64_t e, int64_t m) {
    int64_t r = 1 % m;
    b %= m;
    if (b < 0) b += m;
    while (e > 0) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}

static int64_t gcd64(int64_t a, int64_t b) {
    if (a < 0) a = -a;
    if (b < 0) b = -b;
    while (b) {
        int64_t t = a % b;
        a = b;
        b = t;
    }
    return a;
}

static int is_prime_int(int n) {
    if (n < 2) return 0;
    for (int q = 2; (int64_t)q * q <= n; q++)
        if (n % q == 0) return 0;
    return 1;
}

/* Z_m x| Z_k: element (a,b) -> a*k+b, (a,b)(c,e) = (a + r^b c, b + e). */
static int build_semidirect(int m, int k, int r) {
    if (m < 1 || k < 1 || (int64_t)m * k > MAXG) return 0;
    r %= m;
    if (r < 0) r += m;
    if (powmod(r, k, m) != 1 % m) return 0;
    if (gcd64(r, m) != 1) return 0;
    G = m * k;
    MT = malloc(sizeof(int) * (size_t)G * G);
    int *pw = malloc(sizeof(int) * (size_t)k);
    for (int b = 0; b < k; b++) pw[b] = (int)powmod(r, b, m);
    for (int x = 0; x < G; x++) {
        int a = x / k, b = x % k;
        for (int y = 0; y < G; y++) {
            int c = y / k, e = y % k;
            int a2 = (int)(((int64_t)a + (int64_t)pw[b] * c) % m);
            int b2 = (b + e) % k;
            MT[(size_t)x * G + y] = a2 * k + b2;
        }
    }
    free(pw);
    ID = 0;
    return 1;
}

/* AGL(1,p): maps x -> a x + b, a in 1..p-1, b in 0..p-1; index (a-1)*p + b. */
static int build_agl(int p) {
    if (p < 2 || !is_prime_int(p) || p * (p - 1) > MAXG) return 0;
    G = p * (p - 1);
    MT = malloc(sizeof(int) * (size_t)G * G);
    for (int x = 0; x < G; x++) {
        int a = x / p + 1, b = x % p;
        for (int y = 0; y < G; y++) {
            int c = y / p + 1, e = y % p;
            int a2 = (a * c) % p;
            int b2 = (a * e + b) % p;
            MT[(size_t)x * G + y] = (a2 - 1) * p + b2;
        }
    }
    ID = 0;
    return 1;
}

/* Canonical code of a 2x2 matrix up to scalars (proj = 1: all nonzero
   scalars, PGL) or up to sign (proj = 0: +-1, PSL). */
static int canon_code(const int *m, int p, int proj) {
    int best = -1;
    for (int lam = 1; lam < p; lam++) {
        if (!proj && lam != 1 && lam != p - 1) continue;
        int c = (((lam * m[0]) % p) * p + (lam * m[1]) % p) * p;
        c = (c + (lam * m[2]) % p) * p + (lam * m[3]) % p;
        if (best < 0 || c < best) best = c;
    }
    return best;
}

static int build_proj(int p, int psl) {
    if (p < 3 || !is_prime_int(p)) return 0;
    int P4 = p * p * p * p;
    int *idof = malloc(sizeof(int) * (size_t)P4);
    int *rep = malloc(sizeof(int) * 4 * (size_t)MAXG);
    for (int i = 0; i < P4; i++) idof[i] = -1;
    int cnt = 0, bad = 0;
    for (int a = 0; a < p; a++)
    for (int b = 0; b < p; b++)
    for (int c = 0; c < p; c++)
    for (int dd = 0; dd < p; dd++) {
        int det = ((a * dd - b * c) % p + p) % p;
        if (psl ? (det != 1) : (det == 0)) continue;
        int m[4] = {a, b, c, dd};
        int plain = ((a * p + b) * p + c) * p + dd;
        if (canon_code(m, p, !psl) != plain) continue;
        if (cnt >= MAXG) {
            bad = 1;
            continue;
        }
        idof[plain] = cnt;
        rep[4 * cnt] = a;
        rep[4 * cnt + 1] = b;
        rep[4 * cnt + 2] = c;
        rep[4 * cnt + 3] = dd;
        cnt++;
    }
    if (bad || cnt < 1) {
        free(idof);
        free(rep);
        return 0;
    }
    G = cnt;
    MT = malloc(sizeof(int) * (size_t)G * G);
    int ok = 1;
    for (int x = 0; x < G; x++) {
        int a1 = rep[4 * x], b1 = rep[4 * x + 1], c1 = rep[4 * x + 2], d1 = rep[4 * x + 3];
        for (int y = 0; y < G; y++) {
            int a2 = rep[4 * y], b2 = rep[4 * y + 1], c2 = rep[4 * y + 2], d2 = rep[4 * y + 3];
            int m[4] = {
                (a1 * a2 + b1 * c2) % p,
                (a1 * b2 + b1 * d2) % p,
                (c1 * a2 + d1 * c2) % p,
                (c1 * b2 + d1 * d2) % p
            };
            int v = idof[canon_code(m, p, !psl)];
            if (v < 0) {
                ok = 0;
                v = 0;
            }
            MT[(size_t)x * G + y] = v;
        }
    }
    int I[4] = {1, 0, 0, 1};
    int idv = idof[canon_code(I, p, !psl)];
    free(idof);
    free(rep);
    if (!ok || idv < 0) {
        free(MT);
        return 0;
    }
    ID = idv;
    return 1;
}

static void set_dart(int l, int i, int p, int s) {
    int is = INV[s];
    int *row = nbr + (size_t)l * N;
    int Ab = i * G, Bb = (K + p) * G;
    for (int g = 0; g < G; g++) {
        row[Ab + g] = Bb + MUL(g, s);
        row[Bb + g] = Ab + MUL(g, is);
    }
}

/* out[v] bit b set iff some vertex of block b (its identity fibre) is within
   DIAM steps of v. By group symmetry this decides the diameter. */
static void compute_reach(uint8_t *out) {
    memset(out, 0, (size_t)N);
    for (int b = 0; b < 2 * K; b++) out[b * G + ID] = (uint8_t)(1u << b);
    for (int t = 0; t < DIAM; t++) {
        int changed = 0;
        for (int v = 0; v < N; v++) {
            uint8_t x = out[v];
            for (int l = 0; l < DEG; l++) x |= out[nbr[(size_t)l * N + v]];
            tmpb[v] = x;
            if (x != out[v]) changed = 1;
        }
        if (!changed) break;
        memcpy(out, tmpb, (size_t)N);
    }
}

static int64_t unreached(const uint8_t *r) {
    int64_t s = 0;
    for (int v = 0; v < N; v++) s += POP[r[v]];
    return (int64_t)2 * K * N - s;
}

static int dupcount(void) {
    int n = DEG * K, dup = 0;
    for (int e = 0; e < n; e++) {
        int i = e % K;
        for (int f = i; f < e; f += K) {
            if (lay[f] == lay[e] && vol[f] == vol[e]) {
                dup++;
                break;
            }
        }
    }
    return dup;
}

static int64_t total_cost(const uint8_t *r) {
    return unreached(r) + (int64_t)PEN * dupcount();
}

static int run_trial(int iters, int patience, int reinit) {
    int n = DEG * K;
    timed_out = 0;
    if (reinit) {
        for (int l = 0; l < DEG; l++) {
            int perm[MAXK];
            for (int i = 0; i < K; i++) perm[i] = i;
            for (int i = K - 1; i > 0; i--) {
                int j = rndint(i + 1);
                int t = perm[i];
                perm[i] = perm[j];
                perm[j] = t;
            }
            for (int i = 0; i < K; i++) lay[l * K + i] = perm[i];
        }
        for (int e = 0; e < n; e++) vol[e] = rndint(G);
    }
    for (int l = 0; l < DEG; l++)
        for (int i = 0; i < K; i++)
            set_dart(l, i, lay[l * K + i], vol[l * K + i]);

    compute_reach(cur);
    int64_t cost = total_cost(cur);
    double c0 = cost > 1 ? (double)cost : 1.0;
    int64_t best_cost = cost;
    int last = 0;

    for (int t = 0; t < iters && cost != 0; t++) {
        if (t - last > patience) break;
        if ((t & 31) == 0 && elapsed() > TL) {
            timed_out = 1;
            break;
        }
        double temp = 0.01 * c0 * (1.0 - (double)t / iters);
        if (temp < 0.3) temp = 0.3;
        int64_t c2 = 0;
        double mv = rnd01();

        if (K >= 2 && mv < 0.25) {
            /* layer swap inside one layer */
            int l = rndint(DEG);
            int i1 = rndint(K);
            int i2 = rndint(K - 1);
            if (i2 >= i1) i2++;
            int e1 = l * K + i1, e2 = l * K + i2;
            int tp = lay[e1];
            lay[e1] = lay[e2];
            lay[e2] = tp;
            set_dart(l, i1, lay[e1], vol[e1]);
            set_dart(l, i2, lay[e2], vol[e2]);
            compute_reach(scr);
            c2 = total_cost(scr);
            if (!(c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / temp))) {
                tp = lay[e1];
                lay[e1] = lay[e2];
                lay[e2] = tp;
                set_dart(l, i1, lay[e1], vol[e1]);
                set_dart(l, i2, lay[e2], vol[e2]);
                continue;
            }
        } else if (DEG >= 2 && mv < 0.40) {
            /* voltage exchange for one base vertex between two layers */
            int l1 = rndint(DEG);
            int l2 = rndint(DEG - 1);
            if (l2 >= l1) l2++;
            int i = rndint(K);
            int e1 = l1 * K + i, e2 = l2 * K + i;
            int v1 = vol[e1], v2 = vol[e2];
            if (v1 == v2) continue;
            vol[e1] = v2;
            vol[e2] = v1;
            set_dart(l1, i, lay[e1], vol[e1]);
            set_dart(l2, i, lay[e2], vol[e2]);
            compute_reach(scr);
            c2 = total_cost(scr);
            if (!(c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / temp))) {
                vol[e1] = v1;
                vol[e2] = v2;
                set_dart(l1, i, lay[e1], vol[e1]);
                set_dart(l2, i, lay[e2], vol[e2]);
                continue;
            }
        } else {
            /* single voltage change, defect-targeted with probability 0.4 */
            int l = rndint(DEG), i = rndint(K);
            if (rnd01() < 0.4) {
                int u = -1, cnt = 0;
                for (int v = 0; v < N; v++) {
                    if (cur[v] != FULL) {
                        cnt++;
                        if (rndint(cnt) == 0) u = v;
                    }
                }
                if (u >= 0) {
                    int block = u / G;
                    if (block < K) {
                        i = block;
                    } else {
                        int p = block - K;
                        i = -1;
                        for (int j = 0; j < K; j++) {
                            if (lay[l * K + j] == p) {
                                i = j;
                                break;
                            }
                        }
                        if (i < 0) continue;
                    }
                }
            }
            int e = l * K + i;
            int old = vol[e];
            int nw = rndint(G);
            if (nw == old) continue;
            vol[e] = nw;
            set_dart(l, i, lay[e], nw);
            compute_reach(scr);
            c2 = total_cost(scr);
            if (!(c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / temp))) {
                vol[e] = old;
                set_dart(l, i, lay[e], old);
                continue;
            }
        }

        /* accepted */
        uint8_t *tb = cur;
        cur = scr;
        scr = tb;
        cost = c2;
        if (cost < best_cost) {
            best_cost = cost;
            last = t;
        }
    }
    LASTCOST = cost;
    return cost == 0;
}

int main(int argc, char **argv) {
    if (argc < 10) {
        printf("0 0\n");
        return 0;
    }
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    int gtype = atoi(argv[3]);
    int p1 = atoi(argv[4]), p2 = atoi(argv[5]), p3 = atoi(argv[6]);
    K = atoi(argv[7]);
    unsigned long long seed = strtoull(argv[8], NULL, 10);
    TL = atof(argv[9]);
    tstart = now_s();

    rs = (seed + 1) * 0x9E3779B97F4A7C15ULL ^ 0xD1B54A32D192ED03ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 8; i++) rnd64();
    for (int x = 0; x < 256; x++) {
        int c = 0;
        for (int y = x; y; y >>= 1) c += y & 1;
        POP[x] = (uint8_t)c;
    }

    if (DEG < 3 || DIAM < 3 || K < 1 || K > MAXK) {
        printf("0 0\n");
        return 0;
    }

    int ok = 0;
    if (gtype == 0) ok = build_semidirect(p1, p2, p3);
    else if (gtype == 1) ok = build_agl(p1);
    else if (gtype == 2) ok = build_proj(p1, 1);
    else if (gtype == 3) ok = build_proj(p1, 0);
    if (!ok || G < 1) {
        printf("0 0\n");
        return 0;
    }

    INV = malloc(sizeof(int) * (size_t)G);
    for (int x = 0; x < G; x++) {
        INV[x] = -1;
        for (int y = 0; y < G; y++) {
            if (MUL(x, y) == ID) {
                INV[x] = y;
                break;
            }
        }
        if (INV[x] < 0) {
            printf("0 0\n");
            return 0;
        }
    }

    N = 2 * K * G;
    FULL = (uint8_t)((1u << (2 * K)) - 1);
    nbr = malloc(sizeof(int) * (size_t)DEG * N);
    lay = malloc(sizeof(int) * (size_t)DEG * K);
    vol = malloc(sizeof(int) * (size_t)DEG * K);
    cur = malloc((size_t)N);
    scr = malloc((size_t)N);
    tmpb = malloc((size_t)N);
    if (!nbr || !lay || !vol || !cur || !scr || !tmpb) {
        printf("0 0\n");
        return 0;
    }

    int found = 0;
    int fresh = 1;
    while (elapsed() < TL) {
        run_trial(ITERS, PAT, fresh);
        if (LASTCOST == 0) {
            found = 1;
            break;
        }
        if (timed_out) break;
        fresh = (rnd01() < 0.5);
    }

    if (!found) {
        printf("0 0\n");
        return 0;
    }
    int KG = K * G;
    printf("%d %lld\n", N, (long long)KG * DEG);
    for (int u = 0; u < KG; u++)
        for (int l = 0; l < DEG; l++)
            printf("%d %d\n", u, nbr[(size_t)l * N + u]);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Exact construction used as a fallback.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Group families for the C engine.
# Entries: (group type, p1, p2, p3, group order, selection penalty).
# ----------------------------------------------------------------------------

def _primes_upto(n):
    return [p for p in range(2, n + 1)
            if all(p % q for q in range(2, math.isqrt(p) + 1))]


def _families(maxg):
    fams = []
    for p in _primes_upto(60):
        if p * (p - 1) <= maxg:
            fams.append((1, p, 0, 0, p * (p - 1), 0))
    for p in _primes_upto(20):
        if p >= 5:
            if p * (p * p - 1) // 2 <= maxg:
                fams.append((2, p, 0, 0, p * (p * p - 1) // 2, 0))
            if p * (p * p - 1) <= maxg:
                fams.append((3, p, 0, 0, p * (p * p - 1), 0))
    for m in range(3, maxg // 2 + 1):
        # dihedral group D_m = Z_m x| Z_2 with r = m - 1; lower priority
        fams.append((0, m, 2, m - 1, 2 * m, 200))
    return fams


# ----------------------------------------------------------------------------
# Main build.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.8 * time_limit, time_limit - 10.0))
    deadline = start + budget

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    if d >= 3 and D >= 3:
        moore = lib.moore_bound(d, D)
        cap = min(moore, 4 * 2 * 2600)
        goal = int(0.27 * moore)
        cands = []
        for gtype, p1, p2, p3, order, pen in _families(2600):
            for K in range(1, 5):
                size = 2 * K * order
                if size <= best_n or size > cap:
                    continue
                cands.append([size, K, gtype, p1, p2, p3, pen])

        used = set()
        while time.monotonic() < deadline - 4.0:
            remaining = deadline - time.monotonic()
            pool = [i for i in range(len(cands))
                    if i not in used and cands[i][0] > best_n]
            if not pool:
                break
            g_now = max(goal, best_n + 1)
            i = min(pool, key=lambda j: abs(cands[j][0] - g_now) + cands[j][6])
            used.add(i)
            size, K, gtype, p1, p2, p3, _ = cands[i]
            slice_s = min(remaining, max(6.0, remaining / 3.0))
            try:
                text = lib.run_c(
                    C_SOURCE,
                    [d, D, gtype, p1, p2, p3, K, int(seed) & 0x7FFFFFFF, round(slice_s, 2)],
                    timeout=slice_s + 20.0,
                )
                n2, e2 = lib.parse_graph_text(text)
                if n2 > 0:
                    consider(n2, e2)
            except Exception:
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
