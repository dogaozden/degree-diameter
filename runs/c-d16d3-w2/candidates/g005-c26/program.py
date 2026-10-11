import random
import time

import lib


# ----------------------------------------------------------------------------
# New idea: exact-capacity packing of arc vertices.
#
# Start from PG(2,q) incidence, which is (q+1)-regular with diameter 3. Pick a
# set SA of points so that every line contains at most s = d-q-1 points of SA.
# Each chosen point becomes a new A-vertex joined to the q+1 lines through it.
# Lines then gain at most s extra degree, so degrees stay <= d. Likewise pick a
# set SB of lines (load <= s on points) and add a new B-vertex per chosen line.
# The two packings use independent spare degree, so they do not interact.
#
# Diameter stays <= 3: adding vertices never breaks the PG distances, and any
# pair involving a new vertex has a path of length <= 3 through the PG graph.
# Extra edges only shorten paths, so a final greedy fill of spare degree between
# opposite sides is also safe.
#
# The packing is a maximum set-packing problem, solved by simulated annealing in
# C with insertion moves that evict blocking items.
# ----------------------------------------------------------------------------

PACK_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MI 2048
#define MK 128

static int nI, nT, cap;
static int tg[MI][MK], td[MI];
static int load[MI];
static int chosen[MI], memb[MI], nmemb, pos[MI];
static int bestset[MI], nbest;
static int mark[MI], stamp;
static int cand[MI], rem[MK];
static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd64(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndi(int n) { return (int)(rnd64() % (uint64_t)n); }
static double rndu(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static int covers(int c, int t) {
    for (int k = 0; k < td[c]; k++) if (tg[c][k] == t) return 1;
    return 0;
}

static void addi(int p) {
    chosen[p] = 1;
    pos[p] = nmemb;
    memb[nmemb++] = p;
    for (int k = 0; k < td[p]; k++) load[tg[p][k]]++;
}

static void remi(int p) {
    chosen[p] = 0;
    int i = pos[p];
    int last = memb[--nmemb];
    memb[i] = last;
    pos[last] = i;
    for (int k = 0; k < td[p]; k++) load[tg[p][k]]--;
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    nI = atoi(argv[1]);
    cap = atoi(argv[2]);
    double budget = atof(argv[3]);
    rs ^= (uint64_t)strtoull(argv[4], NULL, 10) * 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 10; i++) rnd64();

    int N, M;
    if (scanf("%d %d", &N, &M) != 2 || nI < 1 || nI > MI || N - nI < 1 || N - nI > MI || cap < 1) {
        printf("0 0\n");
        return 0;
    }
    nT = N - nI;
    for (int i = 0; i < M; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) break;
        if (u > v) { int t = u; u = v; v = t; }
        if (u < 0 || u >= nI || v < nI || v >= N) continue;
        if (td[u] >= MK) continue;
        tg[u][td[u]++] = v - nI;
    }

    static int ord[MI];
    for (int i = 0; i < nI; i++) ord[i] = i;
    for (int i = nI - 1; i > 0; i--) {
        int j = rndi(i + 1);
        int t = ord[i]; ord[i] = ord[j]; ord[j] = t;
    }
    for (int k = 0; k < nI; k++) {
        int p = ord[k];
        int ok = 1;
        for (int j = 0; j < td[p]; j++) if (load[tg[p][j]] >= cap) { ok = 0; break; }
        if (ok) addi(p);
    }
    nbest = nmemb;
    memcpy(bestset, memb, sizeof(int) * nmemb);

    clock_t c0 = clock();
    double T = 0.5, T0 = 0.5, T1 = 0.05;
    long it = 0;
    stamp = 0;
    while (1) {
        if ((it & 63) == 0) {
            double el = (double)(clock() - c0) / CLOCKS_PER_SEC;
            if (el >= budget) break;
            double fr = budget > 0 ? el / budget : 1.0;
            T = T0 * pow(T1 / T0, fr);
        }
        it++;
        if (nmemb > 0 && rndu() < 0.03) {
            int q = memb[rndi(nmemb)];
            if (rndu() < exp(-1.0 / T)) remi(q);
            continue;
        }
        int p = rndi(nI);
        if (chosen[p]) continue;
        stamp++;
        int nr = 0;
        for (int k = 0; k < td[p]; k++) {
            int t = tg[p][k];
            if (load[t] < cap) continue;
            int nc = 0;
            for (int i = 0; i < nmemb; i++) if (covers(memb[i], t)) cand[nc++] = memb[i];
            if (nc == 0) continue;
            int c = cand[rndi(nc)];
            if (mark[c] != stamp) { mark[c] = stamp; rem[nr++] = c; }
        }
        int delta = 1 - nr;
        if (delta >= 0 || rndu() < exp(delta / T)) {
            for (int i = 0; i < nr; i++) remi(rem[i]);
            addi(p);
            if (nmemb > nbest) {
                nbest = nmemb;
                memcpy(bestset, memb, sizeof(int) * nmemb);
            }
        }
    }

    printf("%d %d\n", nbest, nbest);
    for (int i = 0; i < nbest; i++) printf("%d 0\n", bestset[i]);
    return 0;
}
"""


def _best_q(d):
    """Prime power q <= d-1 maximizing the packing-based order estimate 2m + 2*floor(s*m/(q+1))."""
    best = None
    for q in range(2, d):
        if q + 1 > d or not lib.is_prime_power(q):
            continue
        s = d - q - 1
        m = q * q + q + 1
        est = 2 * m + 2 * (s * m // (q + 1))
        if best is None or est > best[0]:
            best = (est, q)
    return best[1] if best else None


def _best_pack(m, item_edges, cap, budget, seed, reps):
    """Run the C packing `reps` times; return the largest chosen item list (item indices < m)."""
    best = []
    if cap <= 0 or budget < 0.1:
        return best
    for r in range(reps):
        try:
            out = lib.run_c(PACK_SOURCE, [m, cap, round(budget, 3), seed * 131 + r],
                            stdin_graph=(2 * m, item_edges), timeout=budget + 10.0)
            _, pairs = lib.parse_graph_text(out)
        except Exception:
            continue
        cur = sorted({u for u, _ in pairs if 0 <= u < m})
        if len(cur) > len(best):
            best = cur
    return best


def _fill(n, edges, A, B, d, rng):
    """Greedily add edges between A and B while both ends have spare degree (keeps validity and diameter)."""
    deg = [0] * n
    es = set()
    for u, v in edges:
        deg[u] += 1
        deg[v] += 1
        es.add((min(u, v), max(u, v)))
    pairs = [(a, b) for a in A for b in B]
    rng.shuffle(pairs)
    out = list(edges)
    for a, b in pairs:
        if deg[a] < d and deg[b] < d:
            key = (min(a, b), max(a, b))
            if key not in es:
                es.add(key)
                deg[a] += 1
                deg[b] += 1
                out.append((a, b))
    return out


def _build_d3(d, q, seed, budget_total):
    """PG(2,q) plus packed arc vertices on both sides, then greedy fill."""
    n2, edges = lib.projective_plane_incidence(q)
    m = n2 // 2
    s = d - q - 1
    pl = [[] for _ in range(m)]   # point -> lines
    lp = [[] for _ in range(m)]   # line -> points
    for i, v in edges:
        j = v - m
        pl[i].append(j)
        lp[j].append(i)
    edges_lp = [(j, m + i) for j in range(m) for i in lp[j]]

    reps = 3
    per = budget_total / (2 * reps)
    SA = _best_pack(m, list(edges), s, per, seed, reps)         # chosen points
    SB = _best_pack(m, edges_lp, s, per, seed + 101, reps)      # chosen lines

    na, nb = len(SA), len(SB)
    n = 2 * m + na + nb
    E = list(edges)
    for t, P in enumerate(SA):
        x = 2 * m + t
        E.extend((x, m + j) for j in pl[P])
    for t, L in enumerate(SB):
        y = 2 * m + na + t
        E.extend((i, y) for i in lp[L])
    A = list(range(m)) + list(range(2 * m, 2 * m + na))
    B = list(range(m, 2 * m)) + list(range(2 * m + na, n))
    E = _fill(n, E, A, B, d, random.Random(seed))
    return n, E


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    best = lib.haar_graph(d, range(d))  # K_{d,d}, diameter 2: always valid for D >= 2

    if D == 3 and d >= 3:
        try:
            q = _best_q(d)
            if q is not None:
                left = 0.72 * time_limit - 1.5 - (time.monotonic() - t0)
                g = _build_d3(d, q, seed, max(left, 0.0))
                if g[0] > best[0] and lib.is_valid(g[0], g[1], d, D):
                    best = g
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
