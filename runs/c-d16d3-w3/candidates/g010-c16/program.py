"""Capacitated multiset packing on projective-plane incidence graphs (diameter 3).

Start from PG(2, q) incidence (points 0..m-1, lines m..2m-1). Each side may add
new "twin" vertices: a new vertex copies the neighbourhood of an old vertex x on
the opposite side. An old vertex y can take at most cap[y] = d - deg(y) new
neighbours in total. So the problem is an integer packing: pick a multiset of
entries x maximising the count, subject to per-target loads <= cap.

New idea (not in the parent): the packing is solved in C by penalised simulated
annealing with add, remove and swap moves, plus restarts and a greedy polish. The
LP bound s*m/(q+1) is a useful target, and the annealer can get close to it.
The C engine verifies its final graph by BFS (degree, diameter D, connectivity)
and prints the input unchanged if verification fails. Python checks again with
lib.is_valid and keeps a valid fallback.
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

static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd64(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rndint(int k) { return (int)(rnd64() % (uint64_t)k); }

static double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static double now_s(void) { return (double)clock() / (double)CLOCKS_PER_SEC; }

/* State of one side's packing. Entry x uses base neighbours lst[off[x]..off[x+1]). */
typedef struct {
    const int *off, *lst, *cap;
    int *cnt, *load;
    int total, ov;
} St;

static void apply_move(St *S, int x, int sg) {
    for (int k = S->off[x]; k < S->off[x + 1]; k++) {
        int y = S->lst[k];
        int b = S->load[y], a = b + sg, c = S->cap[y];
        int ob = b > c ? b - c : 0;
        int oa = a > c ? a - c : 0;
        S->ov += oa - ob;
        S->load[y] = a;
    }
    S->cnt[x] += sg;
    S->total += sg;
}

static int can_add(const St *S, int x) {
    for (int k = S->off[x]; k < S->off[x + 1]; k++) {
        int y = S->lst[k];
        if (S->load[y] >= S->cap[y]) return 0;
    }
    return 1;
}

/* Maximise sum cnt[x] subject to load[y] <= cap[y]. Writes the best feasible
   counts into bestcnt (size n) and returns the total. */
static int opt_side(int n, const int *off, const int *lst, const int *cap,
                    const int *ent, int nent, double t_end, double lam,
                    long iters, int *bestcnt) {
    memset(bestcnt, 0, sizeof(int) * (size_t)n);
    if (nent <= 0) return 0;
    int *cnt = calloc((size_t)n, sizeof(int));
    int *load = calloc((size_t)n, sizeof(int));
    int opx[4], opg[4];
    int best = 0;

    while (now_s() < t_end) {
        memset(cnt, 0, sizeof(int) * (size_t)n);
        memset(load, 0, sizeof(int) * (size_t)n);
        St S = { off, lst, cap, cnt, load, 0, 0 };
        for (int t = 0; t < 3 * nent; t++) {
            int x = ent[rndint(nent)];
            if (can_add(&S, x)) apply_move(&S, x, 1);
        }
        for (long it = 0; it < iters; it++) {
            if ((it & 1023) == 0 && now_s() >= t_end) break;
            double T = 0.7 * pow(0.03 / 0.7, (double)it / (double)iters);
            double F0 = (double)S.total - lam * (double)S.ov;
            int nops = 0;
            int r = rndint(10);
            if (r < 4) {
                int x = ent[rndint(nent)];
                apply_move(&S, x, 1);
                opx[nops] = x;
                opg[nops++] = 1;
            } else {
                int xr = -1;
                for (int tr = 0; tr < 80 && xr < 0; tr++) {
                    int x = ent[rndint(nent)];
                    if (cnt[x] > 0) xr = x;
                }
                if (xr < 0) continue;
                apply_move(&S, xr, -1);
                opx[nops] = xr;
                opg[nops++] = -1;
                if (r >= 7) {
                    int x = ent[rndint(nent)];
                    apply_move(&S, x, 1);
                    opx[nops] = x;
                    opg[nops++] = 1;
                }
            }
            double F1 = (double)S.total - lam * (double)S.ov;
            double dl = F1 - F0;
            if (dl >= 0.0 || rnd01() < exp(dl / T)) {
                if (S.ov == 0 && S.total > best) {
                    best = S.total;
                    memcpy(bestcnt, cnt, sizeof(int) * (size_t)n);
                }
            } else {
                for (int k = nops - 1; k >= 0; k--) apply_move(&S, opx[k], -opg[k]);
            }
        }
    }

    /* Greedy polish of the best packing. */
    memset(cnt, 0, sizeof(int) * (size_t)n);
    memset(load, 0, sizeof(int) * (size_t)n);
    memcpy(cnt, bestcnt, sizeof(int) * (size_t)n);
    St P = { off, lst, cap, cnt, load, 0, 0 };
    for (int i = 0; i < nent; i++) {
        int x = ent[i];
        if (cnt[x] == 0) continue;
        for (int k = off[x]; k < off[x + 1]; k++) load[lst[k]] += cnt[x];
        P.total += cnt[x];
    }
    for (int y = 0; y < n; y++)
        if (load[y] > cap[y]) P.ov += load[y] - cap[y];
    if (P.ov == 0) {
        for (int pass = 0; pass < 3; pass++)
            for (int i = 0; i < nent; i++) {
                int x = ent[i];
                while (can_add(&P, x)) apply_move(&P, x, 1);
            }
        memcpy(bestcnt, cnt, sizeof(int) * (size_t)n);
    } else {
        memset(bestcnt, 0, sizeof(int) * (size_t)n);
        P.total = 0;
    }
    free(cnt);
    free(load);
    return P.total;
}

static void print_graph(int n, long m, const int *eu, const int *ev) {
    printf("%d %ld\n", n, m);
    for (long i = 0; i < m; i++) printf("%d %d\n", eu[i], ev[i]);
}

/* Exact check: max degree <= d, no self-loops, every pair within distance D. */
static int verify(int N, long M, const int *ea, const int *eb, int d, int D) {
    int *dg = calloc((size_t)N, sizeof(int));
    for (long i = 0; i < M; i++) {
        if (ea[i] == eb[i]) { free(dg); return 0; }
        dg[ea[i]]++;
        dg[eb[i]]++;
    }
    for (int v = 0; v < N; v++)
        if (dg[v] > d) { free(dg); return 0; }
    int *o = malloc(sizeof(int) * (size_t)(N + 1));
    int *f = malloc(sizeof(int) * (size_t)(N + 1));
    int *adj = malloc(sizeof(int) * (2 * (size_t)M + 1));
    int *dist = malloc(sizeof(int) * (size_t)N);
    int *q = malloc(sizeof(int) * (size_t)N);
    o[0] = 0;
    for (int v = 0; v < N; v++) o[v + 1] = o[v] + dg[v];
    memcpy(f, o, sizeof(int) * (size_t)(N + 1));
    for (long i = 0; i < M; i++) {
        adj[f[ea[i]]++] = eb[i];
        adj[f[eb[i]]++] = ea[i];
    }
    int ok = 1;
    for (int s = 0; s < N && ok; s++) {
        for (int v = 0; v < N; v++) dist[v] = -1;
        int h = 0, t = 0;
        q[t++] = s;
        dist[s] = 0;
        while (h < t) {
            int u = q[h++];
            if (dist[u] >= D) continue;
            for (int j = o[u]; j < o[u + 1]; j++) {
                int v = adj[j];
                if (dist[v] < 0) {
                    dist[v] = dist[u] + 1;
                    q[t++] = v;
                }
            }
        }
        if (t != N) ok = 0;
    }
    free(dg); free(o); free(f); free(adj); free(dist); free(q);
    return ok;
}

int main(int argc, char **argv) {
    int d = argc > 1 ? atoi(argv[1]) : 3;
    int D = argc > 2 ? atoi(argv[2]) : 3;
    long seed = argc > 3 ? atol(argv[3]) : 1;
    double budget = argc > 4 ? atof(argv[4]) : 5.0;

    rs = (uint64_t)seed * 0x9E3779B97F4A7C15ULL + 0x2545F4914F6CDD1DULL;
    if (rs == 0) rs = 1;
    double t0 = now_s();
    double t_end = t0 + budget;

    int n = 0, m = 0;
    if (scanf("%d %d", &n, &m) != 2 || n <= 0 || m < 0) {
        printf("0 0\n");
        return 0;
    }
    int *eu = malloc(sizeof(int) * (size_t)(m + 1));
    int *ev = malloc(sizeof(int) * (size_t)(m + 1));
    for (int i = 0; i < m; i++) {
        if (scanf("%d %d", &eu[i], &ev[i]) != 2) { printf("0 0\n"); return 0; }
        if (eu[i] < 0 || eu[i] >= n || ev[i] < 0 || ev[i] >= n) { printf("0 0\n"); return 0; }
    }

    int *deg = calloc((size_t)n, sizeof(int));
    for (int i = 0; i < m; i++) { deg[eu[i]]++; deg[ev[i]]++; }
    int *off = malloc(sizeof(int) * (size_t)(n + 1));
    off[0] = 0;
    for (int v = 0; v < n; v++) off[v + 1] = off[v] + deg[v];
    int *lst = malloc(sizeof(int) * (2 * (size_t)m + 1));
    int *fp = malloc(sizeof(int) * (size_t)(n + 1));
    memcpy(fp, off, sizeof(int) * (size_t)(n + 1));
    for (int i = 0; i < m; i++) {
        lst[fp[eu[i]]++] = ev[i];
        lst[fp[ev[i]]++] = eu[i];
    }

    /* Bipartition by BFS. */
    int *side = malloc(sizeof(int) * (size_t)n);
    int *qu = malloc(sizeof(int) * (size_t)n);
    for (int v = 0; v < n; v++) side[v] = -1;
    int bip = 1;
    for (int s = 0; s < n && bip; s++) {
        if (side[s] >= 0) continue;
        side[s] = 0;
        int h = 0, t = 0;
        qu[t++] = s;
        while (h < t && bip) {
            int u = qu[h++];
            for (int j = off[u]; j < off[u + 1]; j++) {
                int v = lst[j];
                if (side[v] < 0) {
                    side[v] = 1 - side[u];
                    qu[t++] = v;
                } else if (side[v] == side[u]) {
                    bip = 0;
                    break;
                }
            }
        }
    }
    if (!bip) { print_graph(n, m, eu, ev); return 0; }

    int *cap = malloc(sizeof(int) * (size_t)n);
    for (int v = 0; v < n; v++) {
        cap[v] = d - deg[v];
        if (cap[v] < 0) cap[v] = 0;
    }
    int *ent0 = malloc(sizeof(int) * (size_t)n);
    int *ent1 = malloc(sizeof(int) * (size_t)n);
    int nent0 = 0, nent1 = 0;
    for (int v = 0; v < n; v++) {
        if (deg[v] >= 1 && deg[v] <= d) {
            if (side[v] == 0) ent0[nent0++] = v;
            else ent1[nent1++] = v;
        }
    }

    int *bc0 = malloc(sizeof(int) * (size_t)n);
    int *bc1 = malloc(sizeof(int) * (size_t)n);
    double mid = t0 + 0.5 * budget;
    opt_side(n, off, lst, cap, ent0, nent0, mid, 1.5, 1500000L, bc0);
    opt_side(n, off, lst, cap, ent1, nent1, t_end, 1.5, 1500000L, bc1);

    long Ntot = n;
    long Mtot = m;
    for (int v = 0; v < n; v++) {
        long c = (long)bc0[v] + (long)bc1[v];
        Ntot += c;
        Mtot += c * (long)deg[v];
    }
    int *ea = malloc(sizeof(int) * (size_t)(Mtot + 1));
    int *eb = malloc(sizeof(int) * (size_t)(Mtot + 1));
    for (int i = 0; i < m; i++) { ea[i] = eu[i]; eb[i] = ev[i]; }
    long k = m;
    int nxt = n;
    for (int v = 0; v < n; v++) {
        int c = bc0[v] + bc1[v];
        for (int r = 0; r < c; r++) {
            int w = nxt++;
            for (int j = off[v]; j < off[v + 1]; j++) {
                ea[k] = w;
                eb[k] = lst[j];
                k++;
            }
        }
    }

    if (verify(nxt, Mtot, ea, eb, d, D)) {
        printf("%d %ld\n", nxt, Mtot);
        for (long i = 0; i < Mtot; i++) printf("%d %d\n", ea[i], eb[i]);
    } else {
        print_graph(n, m, eu, ev);
    }
    return 0;
}
"""


def _pg_candidates(d):
    """(upper bound on order, q) for each prime power q with q + 1 <= d, largest bound first."""
    out = []
    for q in range(2, d):
        if lib.is_prime_power(q):
            m = q * q + q + 1
            s = d - q - 1
            out.append((2 * m + 2 * (s * m // (q + 1)), q))
    out.sort(reverse=True)
    return out


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]
    if d == 2:
        L = 2 * D
        return L, [(i, (i + 1) % L) for i in range(L)]

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]
    if D < 3:
        return best

    cands = _pg_candidates(d)
    # Plain projective plane incidence graphs are valid for any D >= 3.
    for ub, q in cands:
        if ub <= best_n:
            break
        n0, e0 = lib.projective_plane_incidence(q)
        if n0 > best_n and lib.is_valid(n0, e0, d, D):
            best, best_n = (n0, e0), n0
            break

    # C search: extend each candidate's incidence graph with capacitated twin vertices.
    deadline = t0 + 0.7 * time_limit - 1.0
    for ub, q in cands:
        if ub <= best_n:
            break
        remaining = deadline - time.monotonic()
        if remaining < 1.0:
            break
        n0, e0 = lib.projective_plane_incidence(q)
        budget = remaining
        timeout = max(1.0, time_limit - (time.monotonic() - t0) - 1.0)
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}"],
                            stdin_graph=(n0, e0), timeout=timeout)
            n1, e1 = lib.parse_graph_text(out)
        except Exception:
            continue
        if n1 > best_n and lib.is_valid(n1, e1, d, D):
            best, best_n = (n1, e1), n1

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
