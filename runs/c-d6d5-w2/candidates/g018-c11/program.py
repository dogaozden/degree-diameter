"""Cayley-double growth search for bipartite graphs with max degree d and diameter D.

Phase 1: bipartite doubles of semidirect products Z_m x| Z_k2 (Cayley graphs with d generators,
vertices A_g and B_h, edges A_g - B_{g s}). Simulated annealing over the generator set finds
a group whose double has diameter <= D. Both source classes suffice by left-multiplication symmetry.

Phase 2: start from the best valid graph and insert vertex pairs. A new pair (a, b) takes d-1
edges (x_i, y_i) with distinct endpoints, removes them, and joins a to every y_i and b to every
x_i, plus the edge a-b. Degrees are unchanged. Then degree-preserving double-edge swaps are
annealed on the number of bad ordered pairs until diameter <= D again. A failed attempt is rolled
back to the last valid snapshot.

Python: safe baselines (K_{d,d}, projective plane incidence, Araujo-Pardo & Lopez), then the C
search with the baseline as start graph. Every result is checked with lib.is_valid.
"""
import time

import lib


C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define ITER1 3000
#define ITER2 2500
#define MAXINS 600
#define GCAP 4000
#define MAXC2 12

static struct timespec T0;
static uint64_t rs = 1;
static double DEADLINE, P1_END;
static int DEG, DIAM;
static long long MOORE;

static double elapsed(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)(ts.tv_sec - T0.tv_sec) + 1e-9 * (double)(ts.tv_nsec - T0.tv_nsec);
}

static uint64_t rnd64(void) {
    uint64_t x = rs;
    x ^= x << 13;
    x ^= x >> 7;
    x ^= x << 17;
    rs = x;
    return x;
}

static int rnd_int(int n) { return (int)(rnd64() % (uint64_t)n); }
static double rnd_unit(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static int gcd_i(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
    return a;
}

static int powmod(long long b, int e, int m) {
    long long r = 1 % m, x = b % m;
    while (e) {
        if (e & 1) r = r * x % m;
        x = x * x % m;
        e >>= 1;
    }
    return (int)r;
}

static int popc(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static long long moore_bound(int d, int D) {
    if (D == 0 || d == 0) return 1;
    if (d == 1) return 2;
    if (d == 2) return 2LL * D;
    long long s = 0, p = 1;
    for (int i = 0; i < D; i++) {
        s += p;
        p *= (d - 1);
        if (s > 1000000000LL) break;
    }
    return 2 * s;
}

/* ---------------- best valid graph ---------------- */
static int best_n = 0, best_m = 0;
static int *best_eu = NULL, *best_ev = NULL;

static void set_best(int n, int m, const int *eu, const int *ev) {
    if (n <= best_n || m <= 0) return;
    int *a = malloc(sizeof(int) * (size_t)m);
    int *b = malloc(sizeof(int) * (size_t)m);
    if (!a || !b) { free(a); free(b); return; }
    memcpy(a, eu, sizeof(int) * (size_t)m);
    memcpy(b, ev, sizeof(int) * (size_t)m);
    free(best_eu);
    free(best_ev);
    best_eu = a;
    best_ev = b;
    best_n = n;
    best_m = m;
}

/* ---------------- phase 1: Cayley bipartite doubles ---------------- */
static int CG, CK2, CM, CR;
static int Rp[MAXC2];
static int inv_t[GCAP];
static int Sg[MAXC2], invS[MAXC2];
static int vis[2 * GCAP];
static int vstamp = 0;
static int qa[2 * GCAP], qb[2 * GCAP];

/* (a,b)*(c,e) = (a + r^b c, b + e); element index a*K2 + b. */
static int gmul(int x, int y) {
    int a = x / CK2, b = x % CK2;
    int c = y / CK2, e = y % CK2;
    int ra = (int)(((long long)a + (long long)Rp[b] * c) % CM);
    int rb = (b + e) % CK2;
    return ra * CK2 + rb;
}

static void group_setup(int G, int c2, int m, int r) {
    CG = G;
    CK2 = c2;
    CM = m;
    CR = r;
    Rp[0] = 1 % m;
    for (int b = 1; b < c2; b++) Rp[b] = (int)((long long)Rp[b - 1] * r % m);
    for (int x = 0; x < G; x++) {
        inv_t[x] = -1;
        for (int y = 0; y < G; y++)
            if (gmul(x, y) == 0) { inv_t[x] = y; break; }
    }
}

static int in_S_n(int x, int n) {
    for (int i = 0; i < n; i++) if (Sg[i] == x) return 1;
    return 0;
}

/* Vertices: A_g = g, B_h = CG + h. Edges A_g - B_{g s}. Returns total unreached ordered pairs
   from the two sources A_e and B_e; zero iff diameter <= DIAM. */
static long long cay_cost(void) {
    long long total = 0;
    int N2 = 2 * CG;
    for (int si = 0; si < 2; si++) {
        int src = (si == 0) ? 0 : CG;
        vstamp++;
        int *f = qa, *h = qb;
        int fs = 1, cnt = 1;
        f[0] = src;
        vis[src] = vstamp;
        for (int lv = 0; lv < DIAM && fs > 0; lv++) {
            int ns = 0;
            for (int q = 0; q < fs; q++) {
                int v = f[q];
                if (v < CG) {
                    for (int i = 0; i < DEG; i++) {
                        int u = CG + gmul(v, Sg[i]);
                        if (vis[u] != vstamp) { vis[u] = vstamp; h[ns++] = u; }
                    }
                } else {
                    int hh = v - CG;
                    for (int i = 0; i < DEG; i++) {
                        int u = gmul(hh, invS[i]);
                        if (vis[u] != vstamp) { vis[u] = vstamp; h[ns++] = u; }
                    }
                }
            }
            cnt += ns;
            int *tmp = f; f = h; h = tmp;
            fs = ns;
        }
        total += N2 - cnt;
    }
    return total;
}

static void phase1(void) {
    int cands[MAXC2];
    while (elapsed() < DEADLINE && (elapsed() < P1_END || best_n == 0)) {
        if (best_n >= MOORE) break;
        int gmin = best_n / 2 + 1;
        if (gmin < 3) gmin = 3;
        int spread = gmin / 12 + 3;
        int G = gmin + rnd_int(spread);
        if (G < DEG + 2) G = DEG + 2;
        if (G > GCAP) break;
        int nc = 0;
        for (int c = 1; c <= MAXC2; c++)
            if (G % c == 0 && G / c >= 2) cands[nc++] = c;
        int c2 = cands[rnd_int(nc)];
        int m = G / c2, r = 1;
        if (c2 > 1) {
            int found = 0;
            for (int tr = 0; tr < 200 && !found; tr++) {
                int cand = 1 + rnd_int(m - 1);
                if (gcd_i(cand, m) == 1 && powmod(cand, c2, m) == 1 % m) {
                    r = cand;
                    found = 1;
                }
            }
            if (!found) { c2 = 1; m = G; r = 1; }
        }
        group_setup(G, c2, m, r);
        for (int i = 0; i < DEG; i++) {
            int x;
            do { x = rnd_int(G); } while (in_S_n(x, i));
            Sg[i] = x;
        }
        for (int i = 0; i < DEG; i++) invS[i] = inv_t[Sg[i]];
        long long cost = cay_cost();
        for (int it = 0; it < ITER1 && cost > 0; it++) {
            if ((it & 127) == 0 && elapsed() > DEADLINE) break;
            int i = rnd_int(DEG);
            int old = Sg[i];
            int x;
            do { x = rnd_int(G); } while (in_S_n(x, DEG));
            Sg[i] = x;
            invS[i] = inv_t[x];
            long long newc = cay_cost();
            double T = 1.5 * (1.0 - (double)it / ITER1) + 0.05;
            if (newc <= cost || rnd_unit() < exp(-(double)(newc - cost) / T)) {
                cost = newc;
            } else {
                Sg[i] = old;
                invS[i] = inv_t[old];
            }
        }
        if (cost == 0) {
            int m_e = G * DEG;
            int *eu = malloc(sizeof(int) * (size_t)m_e);
            int *ev = malloc(sizeof(int) * (size_t)m_e);
            if (eu && ev) {
                int k = 0;
                for (int g = 0; g < G; g++)
                    for (int i = 0; i < DEG; i++) {
                        eu[k] = g;
                        ev[k] = G + gmul(g, Sg[i]);
                        k++;
                    }
                set_best(2 * G, m_e, eu, ev);
            }
            free(eu);
            free(ev);
        }
    }
}

/* ---------------- phase 2: vertex-pair insertion + annealing ---------------- */
static int *nbr = NULL, *dg = NULL, *sd = NULL;
static int *snbr = NULL, *sdg = NULL, *ssd = NULL;
static int *umark = NULL, *stk = NULL;
static uint64_t *cur = NULL, *nxt = NULL;
static int N = 0, Vcap = 0, WCAP = 0, sN = 0, usestamp = 0;

static void free_graph(void) {
    free(nbr); free(dg); free(sd);
    free(snbr); free(sdg); free(ssd);
    free(umark); free(stk);
    free(cur); free(nxt);
    nbr = dg = sd = snbr = sdg = ssd = umark = stk = NULL;
    cur = nxt = NULL;
    N = 0;
    Vcap = 0;
}

static int load_graph(int n, int m, const int *eu, const int *ev) {
    free_graph();
    Vcap = n + 2 * MAXINS + 4;
    WCAP = (Vcap + 63) >> 6;
    nbr = malloc(sizeof(int) * (size_t)Vcap * DEG);
    snbr = malloc(sizeof(int) * (size_t)Vcap * DEG);
    dg = calloc((size_t)Vcap, sizeof(int));
    sdg = calloc((size_t)Vcap, sizeof(int));
    sd = malloc(sizeof(int) * (size_t)Vcap);
    ssd = malloc(sizeof(int) * (size_t)Vcap);
    umark = calloc((size_t)Vcap, sizeof(int));
    stk = malloc(sizeof(int) * (size_t)Vcap);
    cur = malloc(sizeof(uint64_t) * (size_t)Vcap * WCAP);
    nxt = malloc(sizeof(uint64_t) * (size_t)Vcap * WCAP);
    if (!nbr || !snbr || !dg || !sdg || !sd || !ssd || !umark || !stk || !cur || !nxt) {
        free_graph();
        return 0;
    }
    N = n;
    for (int v = 0; v < n; v++) sd[v] = -1;
    for (int e = 0; e < m; e++) {
        int u = eu[e], v = ev[e];
        if (u < 0 || v < 0 || u >= n || v >= n || u == v) { free_graph(); return 0; }
        if (dg[u] >= DEG || dg[v] >= DEG) { free_graph(); return 0; }
        nbr[u * DEG + dg[u]++] = v;
        nbr[v * DEG + dg[v]++] = u;
    }
    for (int v = 0; v < n; v++)
        for (int i = 0; i < dg[v]; i++)
            for (int j = 0; j < i; j++)
                if (nbr[v * DEG + i] == nbr[v * DEG + j]) { free_graph(); return 0; }
    for (int s = 0; s < n; s++) {
        if (sd[s] != -1 || dg[s] == 0) continue;
        sd[s] = 0;
        int sp = 0;
        stk[sp++] = s;
        while (sp > 0) {
            int v = stk[--sp];
            for (int i = 0; i < dg[v]; i++) {
                int u = nbr[v * DEG + i];
                if (sd[u] == -1) {
                    sd[u] = 1 - sd[v];
                    stk[sp++] = u;
                } else if (sd[u] == sd[v]) {
                    free_graph();
                    return 0;
                }
            }
        }
    }
    for (int v = 0; v < n; v++) if (sd[v] == -1) sd[v] = 0;
    return 1;
}

/* Bitset BFS: returns the number of ordered pairs at distance > DIAM (0 iff diameter <= DIAM). */
static long long eval_cost(void) {
    int W = (N + 63) >> 6;
    uint64_t *c = cur, *x = nxt;
    memset(c, 0, sizeof(uint64_t) * (size_t)N * (size_t)W);
    for (int v = 0; v < N; v++)
        c[(size_t)v * W + (size_t)(v >> 6)] |= 1ULL << (v & 63);
    for (int lv = 0; lv < DIAM; lv++) {
        for (int v = 0; v < N; v++) {
            uint64_t *xv = x + (size_t)v * W;
            const uint64_t *cv = c + (size_t)v * W;
            memcpy(xv, cv, sizeof(uint64_t) * (size_t)W);
            for (int i = 0; i < dg[v]; i++) {
                const uint64_t *cu = c + (size_t)nbr[v * DEG + i] * W;
                for (int k = 0; k < W; k++) xv[k] |= cu[k];
            }
        }
        uint64_t *tmp = c; c = x; x = tmp;
    }
    long long cost = 0;
    for (int v = 0; v < N; v++) {
        int cnt = 0;
        const uint64_t *cv = c + (size_t)v * W;
        for (int k = 0; k < W; k++) cnt += popc(cv[k]);
        cost += N - cnt;
    }
    return cost;
}

static void save_snapshot(void) {
    sN = N;
    memcpy(snbr, nbr, sizeof(int) * (size_t)N * DEG);
    memcpy(sdg, dg, sizeof(int) * (size_t)N);
    memcpy(ssd, sd, sizeof(int) * (size_t)N);
}

static void restore_snapshot(void) {
    N = sN;
    memcpy(nbr, snbr, sizeof(int) * (size_t)N * DEG);
    memcpy(dg, sdg, sizeof(int) * (size_t)N);
    memcpy(sd, ssd, sizeof(int) * (size_t)N);
}

static int has_edge(int v, int u) {
    for (int i = 0; i < dg[v]; i++) if (nbr[v * DEG + i] == u) return 1;
    return 0;
}

static void rem_entry(int v, int u) {
    for (int i = 0; i < dg[v]; i++)
        if (nbr[v * DEG + i] == u) {
            nbr[v * DEG + i] = nbr[v * DEG + dg[v] - 1];
            dg[v]--;
            return;
        }
}

static void add_entry(int v, int u) {
    nbr[v * DEG + dg[v]] = u;
    dg[v]++;
}

static void replace_entry(int v, int old, int nw) {
    for (int i = 0; i < dg[v]; i++)
        if (nbr[v * DEG + i] == old) { nbr[v * DEG + i] = nw; return; }
}

/* Replace edges a1-b1, a2-b2 by a1-b2, a2-b1 (degree preserving). */
static void rewire(int a1, int b1, int a2, int b2) {
    replace_entry(a1, b1, b2);
    replace_entry(b1, a1, a2);
    replace_entry(a2, b2, b1);
    replace_entry(b2, a2, a1);
}

static int pick_side(int side) {
    for (int tries = 0; tries < 100000; tries++) {
        int v = rnd_int(N);
        if (sd[v] == side && dg[v] > 0) return v;
    }
    return -1;
}

/* Insert a new A-vertex and B-vertex; returns 1 on success, 0 on failure. */
static int insert_pair(void) {
    int need = DEG - 1;
    if (need < 1) return 0;
    int xs[MAXC2], ys[MAXC2], k = 0;
    usestamp++;
    int tries = 0;
    while (k < need && tries < 20000) {
        tries++;
        int v = rnd_int(N);
        if (dg[v] == 0) continue;
        int u = nbr[v * DEG + rnd_int(dg[v])];
        int x = (sd[v] == 0) ? v : u;
        int y = (sd[v] == 0) ? u : v;
        if (umark[x] == usestamp || umark[y] == usestamp) continue;
        umark[x] = usestamp;
        umark[y] = usestamp;
        xs[k] = x;
        ys[k] = y;
        k++;
    }
    if (k < need) return 0;
    for (int i = 0; i < k; i++) {
        rem_entry(xs[i], ys[i]);
        rem_entry(ys[i], xs[i]);
    }
    int na = N, nbv = N + 1;
    N += 2;
    sd[na] = 0;
    sd[nbv] = 1;
    dg[na] = 0;
    dg[nbv] = 0;
    for (int i = 0; i < k; i++) {
        add_entry(na, ys[i]);
        add_entry(ys[i], na);
        add_entry(nbv, xs[i]);
        add_entry(xs[i], nbv);
    }
    add_entry(na, nbv);
    add_entry(nbv, na);
    return 1;
}

static void record_current(void) {
    if (N <= best_n) return;
    int cnt = 0;
    for (int v = 0; v < N; v++) if (sd[v] == 0) cnt += dg[v];
    if (cnt <= 0) return;
    int *eu = malloc(sizeof(int) * (size_t)cnt);
    int *ev = malloc(sizeof(int) * (size_t)cnt);
    if (!eu || !ev) { free(eu); free(ev); return; }
    int k = 0;
    for (int v = 0; v < N; v++)
        if (sd[v] == 0)
            for (int i = 0; i < dg[v]; i++) {
                eu[k] = v;
                ev[k] = nbr[v * DEG + i];
                k++;
            }
    set_best(N, cnt, eu, ev);
    free(eu);
    free(ev);
}

static void phase2(void) {
    if (best_n == 0 || best_n >= MOORE) return;
    if (!load_graph(best_n, best_m, best_eu, best_ev)) return;
    if (eval_cost() != 0) return;
    save_snapshot();
    while (elapsed() < DEADLINE) {
        if (N + 2 > Vcap || N + 2 > MOORE) break;
        int ok = 0;
        for (int t = 0; t < 50 && !ok; t++) ok = insert_pair();
        if (!ok) break;
        long long cc = eval_cost();
        for (int it = 0; it < ITER2 && cc > 0; it++) {
            if ((it & 31) == 0 && elapsed() > DEADLINE) break;
            int a1 = pick_side(0), a2 = pick_side(0);
            if (a1 < 0 || a2 < 0 || a1 == a2) continue;
            int b1 = nbr[a1 * DEG + rnd_int(dg[a1])];
            int b2 = nbr[a2 * DEG + rnd_int(dg[a2])];
            if (b1 == b2 || has_edge(a1, b2) || has_edge(a2, b1)) continue;
            rewire(a1, b1, a2, b2);
            long long nc = eval_cost();
            double T = 1.0 + 1.5 * (1.0 - (double)it / ITER2);
            if (nc <= cc || rnd_unit() < exp(-(double)(nc - cc) / T)) {
                cc = nc;
            } else {
                rewire(a1, b2, a2, b1);
            }
        }
        if (cc == 0) {
            record_current();
            save_snapshot();
        } else {
            restore_snapshot();
        }
    }
}

/* ---------------- main ---------------- */
int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: prog d D seed time_limit\n");
        return 1;
    }
    timespec_get(&T0, TIME_UTC);
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    uint64_t sd0 = strtoull(argv[3], NULL, 10);
    DEADLINE = atof(argv[4]);
    rs = 0x9E3779B97F4A7C15ULL ^ (sd0 * 0xD1B54A32D192ED03ULL + 0x1234567ULL);
    if (rs == 0) rs = 1;
    for (int i = 0; i < 10; i++) rnd64();
    P1_END = 0.4 * DEADLINE;
    if (DEG < 2 || DEG > MAXC2 || DIAM < 1) {
        printf("0 0\n");
        return 0;
    }
    MOORE = moore_bound(DEG, DIAM);

    int n0 = 0, m0 = 0;
    if (scanf("%d %d", &n0, &m0) == 2 && n0 > 0 && m0 > 0 && n0 <= 100000 && m0 <= 1000000) {
        int *eu = malloc(sizeof(int) * (size_t)m0);
        int *ev = malloc(sizeof(int) * (size_t)m0);
        int ok = (eu != NULL && ev != NULL);
        for (int i = 0; ok && i < m0; i++)
            if (scanf("%d %d", &eu[i], &ev[i]) != 2) ok = 0;
        if (ok && load_graph(n0, m0, eu, ev) && eval_cost() == 0) set_best(n0, m0, eu, ev);
        free(eu);
        free(ev);
    }

    if (best_n < MOORE) {
        phase1();
        phase2();
    }

    if (best_m > 0) {
        printf("%d %d\n", best_n, best_m);
        for (int i = 0; i < best_m; i++)
            printf("%d %d\n", best_eu[i], best_ev[i]);
    } else {
        printf("0 0\n");
    }
    return 0;
}
"""


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d; diameter 3."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _araujo(d):
    """Araujo-Pardo & Lopez graph for d = q + 2 with q a prime power >= 3; diameter 3."""
    q = d - 2
    if q >= 3 and lib.is_prime_power(q):
        return lib.araujo_lopez_graph(q)
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
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
            best = (n, list(e))
            best_n = n

    if D >= 3:
        for builder in (_best_pg, _araujo):
            try:
                g = builder(d)
                if g is not None:
                    consider(g[0], g[1])
            except Exception:
                pass

    if best_n >= lib.moore_bound(d, D):
        return best

    elapsed = time.monotonic() - start
    remaining = 0.85 * time_limit - elapsed - 1.0
    if remaining >= 1.0:
        hard = min(remaining + 3.0, time_limit - elapsed - 1.5)
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, f"{remaining:.2f}"],
                            stdin_graph=best, timeout=hard)
            n, e = lib.parse_graph_text(out)
            consider(n, e)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
