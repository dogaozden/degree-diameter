/* r2h: tabu search for the n = 2^(R+1)-2+(2^(R+1)-2)/3 case (R = 6: n = 169) with a fixed Moore tree.
   Tree: root x (A, degree 2), full binary tree to depth R (A at even depth, B at odd depth), 2^R leaves (depth R, A).
   Outer B vertices (O = (2^(R+1)-2)/3, at distance R+1 from x) are free: the search is over the bipartite
   wiring H between leaves (H-degree 2, except 2 leaves with H-degree 1) and outer vertices (H-degree 3).
   Moves: 2-switch of two H-edges, leaf shift (move one H-edge endpoint from a full leaf to a deficit leaf).
   Cost = far = number of unordered pairs at distance > 7 (same as bin/score37), via a bit-parallel 7-step closure.
   Usage: tabu169 R seconds seed out.edges [tmin tmax pert]
*/
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

#define MAXN 192
#define W 3
typedef struct { uint64_t w[W]; } bs;

static int R, n, NT, O, NL, LB;
static int deg[MAXN], adj[MAXN][3], sideA[MAXN];
static bs Ra[MAXN], Rb[MAXN];
static uint64_t rs = 88172645463325252ULL;
static inline uint64_t rnd64(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static inline int rndint(int m) { return (int)(rnd64() % (uint64_t)m); }

static void build_tree(void) {
    NT = (1 << (R + 1)) - 1;
    O = ((1 << (R + 1)) - 2) / 3;
    n = NT + O;
    LB = (1 << R) - 1;
    NL = 1 << R;
    for (int v = 0; v < n; v++) deg[v] = 0;
    for (int d = 0; d < R; d++) {
        int off = (1 << d) - 1, cnt = 1 << d;
        for (int i = 0; i < cnt; i++) {
            int p = off + i;
            for (int c = 0; c < 2; c++) {
                int ch = (1 << (d + 1)) - 1 + 2 * i + c;
                adj[p][deg[p]++] = ch;
                adj[ch][deg[ch]++] = p;
            }
        }
    }
    for (int d = 0; d <= R; d++) {
        int off = (1 << d) - 1, cnt = 1 << d;
        for (int i = 0; i < cnt; i++) sideA[off + i] = (d % 2 == 0);
    }
    for (int v = NT; v < n; v++) sideA[v] = 0;
}

static inline void add_e(int l, int o) { adj[l][deg[l]++] = o; adj[o][deg[o]++] = l; }
static inline void del_e(int l, int o) {
    for (int i = 1; i < deg[l]; i++) if (adj[l][i] == o) { adj[l][i] = adj[l][--deg[l]]; break; }
    for (int i = 0; i < deg[o]; i++) if (adj[o][i] == l) { adj[o][i] = adj[o][--deg[o]]; break; }
}
static inline int has_e(int l, int o) {
    for (int i = 1; i < deg[l]; i++) if (adj[l][i] == o) return 1;
    return 0;
}

static int far_cost(void) {
    for (int v = 0; v < n; v++) { memset(&Ra[v], 0, sizeof(bs)); Ra[v].w[v >> 6] |= 1ULL << (v & 63); }
    bs *cur = Ra, *nx = Rb;
    for (int s = 0; s < 7; s++) {
        for (int v = 0; v < n; v++) {
            bs t = cur[v];
            for (int i = 0; i < deg[v]; i++) {
                const bs *u = &cur[adj[v][i]];
                t.w[0] |= u->w[0]; t.w[1] |= u->w[1]; t.w[2] |= u->w[2];
            }
            nx[v] = t;
        }
        bs *tmp = cur; cur = nx; nx = tmp;
    }
    int tot = 0;
    for (int v = 0; v < n; v++) {
        int c = __builtin_popcountll(cur[v].w[0]) + __builtin_popcountll(cur[v].w[1]) + __builtin_popcountll(cur[v].w[2]);
        tot += n - c;
    }
    return tot / 2;
}

/* far restricted check: same-side pairs at distance > 6 (diagnostic) */
static int same6_cost(void) {
    for (int v = 0; v < n; v++) { memset(&Ra[v], 0, sizeof(bs)); Ra[v].w[v >> 6] |= 1ULL << (v & 63); }
    bs *cur = Ra, *nx = Rb;
    for (int s = 0; s < 6; s++) {
        for (int v = 0; v < n; v++) {
            bs t = cur[v];
            for (int i = 0; i < deg[v]; i++) { const bs *u = &cur[adj[v][i]]; t.w[0] |= u->w[0]; t.w[1] |= u->w[1]; t.w[2] |= u->w[2]; }
            nx[v] = t;
        }
        bs *tmp = cur; cur = nx; nx = tmp;
    }
    int tot = 0;
    for (int v = 0; v < n; v++) {
        int cnt = 0;
        for (int w = 0; w < n; w++) if (sideA[w] == sideA[v] && !((cur[v].w[w >> 6] >> (w & 63)) & 1)) cnt++;
        tot += cnt;
    }
    return tot / 2;
}

static void write_graph(const char *path) {
    FILE *f = fopen(path, "w");
    if (!f) return;
    fprintf(f, "%d\n", n);
    for (int v = 0; v < n; v++) for (int i = 0; i < deg[v]; i++) if (adj[v][i] > v) fprintf(f, "%d %d\n", v, adj[v][i]);
    fclose(f);
}

static int el[512], eo[512], E;
static void collect(void) {
    E = 0;
    for (int l = LB; l < LB + NL; l++) for (int i = 1; i < deg[l]; i++) { el[E] = l; eo[E] = adj[l][i]; E++; }
}

static int tabu_until[128][64];
static int bestE, bestL[512], bestO[512];

static double now(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return t.tv_sec + 1e-9 * t.tv_nsec; }

/* random initial wiring: two deficit leaves, outer deg 3 */
static void random_init(void) {
    int stubs[512], ns = 0;
    int defl[2];
    defl[0] = rndint(NL); do defl[1] = rndint(NL); while (defl[1] == defl[0]);
    for (int l = LB; l < LB + NL; l++) {
        int k = (l - LB == defl[0] || l - LB == defl[1]) ? 1 : 2;
        for (int j = 0; j < k; j++) stubs[ns++] = l;
    }
    /* reset H */
    for (int l = LB; l < LB + NL; l++) deg[l] = 1;
    for (int o = NT; o < n; o++) deg[o] = 0;
    for (;;) {
        for (int i = ns - 1; i > 0; i--) { int j = rndint(i + 1); int t = stubs[i]; stubs[i] = stubs[j]; stubs[j] = t; }
        int ok = 1;
        for (int k = 0; k < ns && ok; k++) for (int k2 = k + 1; k2 < ns && ok; k2++)
            if (k / 3 == k2 / 3 && stubs[k] == stubs[k2]) ok = 0;
        if (ok) break;
    }
    for (int k = 0; k < ns; k++) add_e(stubs[k], NT + k / 3);
}

static void set_state_from_best(void) {
    /* remove all H edges, re-add bestL/bestO */
    for (int l = LB; l < LB + NL; l++) while (deg[l] > 1) { int o = adj[l][deg[l] - 1]; del_e(l, o); }
    for (int o = NT; o < n; o++) deg[o] = 0;
    for (int k = 0; k < bestE; k++) add_e(bestL[k], bestO[k]);
}

int main(int argc, char **argv) {
    if (argc < 5) { fprintf(stderr, "usage: tabu169 R seconds seed out.edges [tmin tmax pert]\n"); return 2; }
    R = atoi(argv[1]);
    double secs = atof(argv[2]);
    rs ^= (uint64_t)atoll(argv[3]) * 0x9E3779B97F4A7C15ULL; if (!rs) rs = 1;
    const char *out = argv[4];
    int tmin = argc > 5 ? atoi(argv[5]) : 10, tmax = argc > 6 ? atoi(argv[6]) : 30;
    long pert = argc > 7 ? atol(argv[7]) : 3000;
    build_tree();
    if (argc > 8) { /* start from an edge list (H edges read, tree edges skipped) */
        FILE *fi = fopen(argv[8], "r"); if (!fi) { fprintf(stderr, "no init file\n"); return 2; }
        int nn, a, b; if (fscanf(fi, "%d", &nn) != 1 || nn != n) { fprintf(stderr, "init n mismatch\n"); return 2; }
        while (fscanf(fi, "%d %d", &a, &b) == 2) {
            int l = a < b ? a : b, o = a < b ? b : a;
            if (l >= LB && l < LB + NL && o >= NT) add_e(l, o);
        }
        fclose(fi);
    } else random_init();
    collect();
    bestE = E; memcpy(bestL, el, sizeof(int) * E); memcpy(bestO, eo, sizeof(int) * E);
    int cur = far_cost();
    int best = cur;
    write_graph(out);
    fprintf(stderr, "n=%d NL=%d O=%d E=%d init far=%d same6=%d\n", n, NL, O, E, cur, same6_cost());
    memset(tabu_until, 0, sizeof tabu_until);
    double t0 = now();
    if (best == 0) { fprintf(stderr, "init already far 0\n"); }
    long iter = 0, lastImp = 0;
    while (best > 0) {
        if ((iter & 15) == 0 && now() - t0 > secs) break;
        iter++;
        collect();
        /* enumerate and evaluate neighbourhood */
        int bmc = 1 << 30, bkind = -1, ba = 0, bb = 0, ties = 0;
        for (int i = 0; i < E; i++) for (int j = i + 1; j < E; j++) {
            int l1 = el[i], o1 = eo[i], l2 = el[j], o2 = eo[j];
            if (l1 == l2 || o1 == o2) continue;
            if (has_e(l1, o2) || has_e(l2, o1)) continue;
            del_e(l1, o1); del_e(l2, o2); add_e(l1, o2); add_e(l2, o1);
            int c = far_cost();
            del_e(l1, o2); del_e(l2, o1); add_e(l1, o1); add_e(l2, o2);
            int tabu = tabu_until[l1 - LB][o2 - NT] > iter || tabu_until[l2 - LB][o1 - NT] > iter;
            if (tabu && c >= best) continue;
            if (c < bmc) { bmc = c; bkind = 0; ba = i; bb = j; ties = 1; }
            else if (c == bmc && rndint(++ties) == 0) { bkind = 0; ba = i; bb = j; }
        }
        /* leaf shifts: edge (l,o) with full leaf l moves to deficit leaf d */
        for (int i = 0; i < E; i++) {
            int l = el[i], o = eo[i];
            if (deg[l] != 3) continue;
            for (int d = LB; d < LB + NL; d++) {
                if (deg[d] != 2 || has_e(d, o)) continue;
                del_e(l, o); add_e(d, o);
                int c = far_cost();
                del_e(d, o); add_e(l, o);
                int tabu = tabu_until[d - LB][o - NT] > iter;
                if (tabu && c >= best) continue;
                if (c < bmc) { bmc = c; bkind = 1; ba = i; bb = d; ties = 1; }
                else if (c == bmc && rndint(++ties) == 0) { bkind = 1; ba = i; bb = d; }
            }
        }
        if (bkind < 0) { /* all tabu: random 2-switch */
            ba = rndint(E); bb = rndint(E); bkind = 0;
            if (el[ba] == el[bb] || eo[ba] == eo[bb]) continue;
        }
        if (bkind == 0) {
            int l1 = el[ba], o1 = eo[ba], l2 = el[bb], o2 = eo[bb];
            if (has_e(l1, o2) || has_e(l2, o1)) continue;
            del_e(l1, o1); del_e(l2, o2); add_e(l1, o2); add_e(l2, o1);
            int T = tmin + rndint(tmax - tmin + 1);
            tabu_until[l1 - LB][o1 - NT] = iter + T; tabu_until[l2 - LB][o2 - NT] = iter + T;
        } else {
            int l = el[ba], o = eo[ba], d = bb;
            del_e(l, o); add_e(d, o);
            int T = tmin + rndint(tmax - tmin + 1);
            tabu_until[l - LB][o - NT] = iter + T;
        }
        cur = bmc;
        if (cur < best) {
            best = cur; lastImp = iter;
            collect(); bestE = E; memcpy(bestL, el, sizeof(int) * E); memcpy(bestO, eo, sizeof(int) * E);
            write_graph(out);
            fprintf(stderr, "iter %ld t=%.1f NEW BEST far=%d (same6=%d)\n", iter, now() - t0, best, same6_cost());
            if (best == 0) break;
        }
        if (iter % 200 == 0) fprintf(stderr, "iter %ld t=%.1f cur=%d best=%d moves=%d\n", iter, now() - t0, cur, best, E);
        if (iter - lastImp > pert) {
            /* perturb: restart from best with 4 random 2-switches */
            set_state_from_best();
            for (int k = 0; k < 4; k++) {
                collect();
                int a = rndint(E), b = rndint(E);
                int l1 = el[a], o1 = eo[a], l2 = el[b], o2 = eo[b];
                if (l1 == l2 || o1 == o2 || has_e(l1, o2) || has_e(l2, o1)) continue;
                del_e(l1, o1); del_e(l2, o2); add_e(l1, o2); add_e(l2, o1);
            }
            cur = far_cost();
            lastImp = iter;
            fprintf(stderr, "iter %ld restart from best, cur=%d\n", iter, cur);
        }
    }
    fprintf(stderr, "done iters=%ld best=%d time=%.1f\n", iter, best, now() - t0);
    printf("best %d\n", best);
    return 0;
}
