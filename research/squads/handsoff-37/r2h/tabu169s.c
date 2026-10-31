/* r2h: symmetric version of tabu169.c. The Moore tree around x (root, degree 2) is kept; an involution t of the tree
   fixes only x: at tree level i (1-based, i = 1 is the root's children) it flips the branch choice when bit (i-1) of
   MASK is set (MASK must have bit 0 set so that t moves every vertex except x). Outer B vertices are paired by
   sigma(2k) = 2k+1 (WLOG). The wiring H is t-invariant: (l,o) in H <=> (t l, sigma o) in H.
   Moves act on orbits: 2-switch of two orbit representatives (two patterns), and a leaf shift of an orbit to a deficit
   leaf d (and t d). Deficit leaves are {d, t d}.
   Usage: tabu169s R MASK seconds seed out.edges [tmin tmax pert]
*/
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

#define MAXN 192
#define W 3
typedef struct { uint64_t w[W]; } bs;

static int R, MASK, n, NT, O, NL, LB;
static int deg[MAXN], adj[MAXN][3], sideA[MAXN], tm[MAXN];
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
    for (int v = 0; v < NT; v++) {
        int d = 0; while ((1 << (d + 1)) - 1 <= v) d++;
        int p = v - ((1 << d) - 1), M = 0;
        for (int i = 1; i <= d; i++) if ((MASK >> (i - 1)) & 1) M |= 1 << (d - i);
        tm[v] = ((1 << d) - 1) + (p ^ M);
    }
    for (int o = NT; o < n; o++) tm[o] = ((o - NT) % 2 == 0) ? o + 1 : o - 1;
    for (int v = 0; v < n; v++) if (tm[tm[v]] != v) { fprintf(stderr, "not involution at %d\n", v); exit(1); }
    for (int v = 0; v < NT; v++) for (int i = 0; i < deg[v]; i++) {
        int u = adj[v][i], a = tm[v], b = tm[u], ok = 0;
        for (int j = 0; j < deg[a]; j++) if (adj[a][j] == b) ok = 1;
        if (!ok) { fprintf(stderr, "tree edge not preserved %d-%d\n", v, u); exit(1); }
    }
    if (tm[0] != 0) { fprintf(stderr, "root moved\n"); exit(1); }
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

static int symmetric_ok(void) {
    for (int l = LB; l < LB + NL; l++) for (int i = 1; i < deg[l]; i++) {
        int o = adj[l][i];
        if (!has_e(tm[l], tm[o])) return 0;
    }
    return 1;
}

static void write_graph(const char *path) {
    FILE *f = fopen(path, "w");
    if (!f) return;
    fprintf(f, "%d\n", n);
    for (int v = 0; v < n; v++) for (int i = 0; i < deg[v]; i++) if (adj[v][i] > v) fprintf(f, "%d %d\n", v, adj[v][i]);
    fclose(f);
}

static int dl[2];
static double now(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return t.tv_sec + 1e-9 * t.tv_nsec; }

static int tabu_until[128][64];

static void random_init(void) {
    for (long attempt = 0;; attempt++) {
        for (int l = LB; l < LB + NL; l++) deg[l] = 1;
        for (int o = NT; o < n; o++) deg[o] = 0;
        int d0 = LB + rndint(NL);
        dl[0] = d0; dl[1] = tm[d0];
        static int need_l[256], need_o[256];
        for (int l = LB; l < LB + NL; l++) need_l[l] = (l == dl[0] || l == dl[1]) ? 1 : 2;
        for (int o = NT; o < n; o++) need_o[o] = 3;
        for (;;) {
            static int cand[4096][2];
            int nc = 0;
            for (int l = LB; l < LB + NL; l++) {
                if (l > tm[l] || need_l[l] <= 0) continue;
                for (int o = NT; o < n; o++) {
                    if (o > tm[o] || need_o[o] <= 0 || need_o[tm[o]] <= 0) continue;
                    if (has_e(l, o)) continue;
                    cand[nc][0] = l; cand[nc][1] = o; nc++;
                }
            }
            if (nc == 0) break;
            int pick = rndint(nc);
            int l = cand[pick][0], o = cand[pick][1];
            add_e(l, o); add_e(tm[l], tm[o]);
            need_l[l]--; need_l[tm[l]]--; need_o[o]--; need_o[tm[o]]--;
        }
        int done = 1;
        for (int l = LB; l < LB + NL; l++) if (need_l[l] != 0) done = 0;
        for (int o = NT; o < n; o++) if (need_o[o] != 0) done = 0;
        if (done && symmetric_ok()) return;
    }
}

static int ORl[256], ORo[256], NR;
static void collect_reps(void) {
    NR = 0;
    for (int l = LB; l < LB + NL; l++) if (l < tm[l]) for (int i = 1; i < deg[l]; i++) { ORl[NR] = l; ORo[NR] = adj[l][i]; NR++; }
}

static int bestNR, bestRL[256], bestRO[256];
static void save_best(void) {
    collect_reps(); bestNR = NR;
    memcpy(bestRL, ORl, sizeof(int) * NR); memcpy(bestRO, ORo, sizeof(int) * NR);
}
static void load_best(void) {
    for (int l = LB; l < LB + NL; l++) while (deg[l] > 1) { int o = adj[l][deg[l] - 1]; del_e(l, o); }
    for (int o = NT; o < n; o++) deg[o] = 0;
    for (int k = 0; k < bestNR; k++) {
        int l = bestRL[k], o = bestRO[k];
        add_e(l, o); add_e(tm[l], tm[o]);
    }
}
static void recompute_deficits(void) {
    int k = 0;
    for (int ll = LB; ll < LB + NL && k < 2; ll++) if (deg[ll] == 2) dl[k++] = ll;
}

int main(int argc, char **argv) {
    if (argc < 6) { fprintf(stderr, "usage: tabu169s R MASK seconds seed out.edges [tmin tmax pert]\n"); return 2; }
    R = atoi(argv[1]); MASK = atoi(argv[2]);
    if (MASK == 0) { fprintf(stderr, "MASK must be nonzero\n"); return 2; }
    double secs = atof(argv[3]);
    rs ^= (uint64_t)atoll(argv[4]) * 0x9E3779B97F4A7C15ULL; if (!rs) rs = 1;
    const char *out = argv[5];
    int tmin = argc > 6 ? atoi(argv[6]) : 10, tmax = argc > 7 ? atoi(argv[7]) : 30;
    long pert = argc > 8 ? atol(argv[8]) : 3000;
    build_tree();
    random_init();
    recompute_deficits();
    if (!symmetric_ok()) { fprintf(stderr, "init not symmetric\n"); return 1; }
    save_best();
    int cur = far_cost(), best = cur;
    write_graph(out);
    fprintf(stderr, "n=%d NL=%d O=%d MASK=%d init far=%d same6=%d reps=%d\n", n, NL, O, MASK, cur, same6_cost(), NR);
    memset(tabu_until, 0, sizeof tabu_until);
    double t0 = now();
    long iter = 0, lastImp = 0;
    while (best > 0) {
        if ((iter & 7) == 0 && now() - t0 > secs) break;
        iter++;
        collect_reps();
        int bmc = 1 << 30, bkind = -1, ba = 0, bb = 0, bpat = 0, ties = 0;
        for (int i = 0; i < NR; i++) for (int j = i + 1; j < NR; j++) for (int pat = 0; pat < 2; pat++) {
            int l1 = ORl[i], o1 = ORo[i];
            int l2 = ORl[j], o2 = ORo[j];
            if (pat == 1) { l2 = tm[l2]; o2 = tm[o2]; }
            if (l1 == l2 || o1 == o2) continue;
            int A[4][2] = {{l1, o1}, {tm[l1], tm[o1]}, {l2, o2}, {tm[l2], tm[o2]}};
            int N[4][2] = {{l1, o2}, {tm[l1], tm[o2]}, {l2, o1}, {tm[l2], tm[o1]}};
            int okr = 1;
            for (int a = 0; a < 4; a++) for (int b = a + 1; b < 4; b++) if (A[a][0] == A[b][0] && A[a][1] == A[b][1]) okr = 0;
            if (!okr) continue;
            for (int a = 0; a < 4; a++) del_e(A[a][0], A[a][1]);
            int okn = 1;
            for (int a = 0; a < 4 && okn; a++) {
                if (has_e(N[a][0], N[a][1])) okn = 0;
                for (int b = a + 1; b < 4 && okn; b++) if (N[a][0] == N[b][0] && N[a][1] == N[b][1]) okn = 0;
            }
            if (!okn) { for (int a = 0; a < 4; a++) add_e(A[a][0], A[a][1]); continue; }
            for (int a = 0; a < 4; a++) add_e(N[a][0], N[a][1]);
            int c = far_cost();
            for (int a = 0; a < 4; a++) del_e(N[a][0], N[a][1]);
            for (int a = 0; a < 4; a++) add_e(A[a][0], A[a][1]);
            int tabu = tabu_until[N[0][0] - LB][N[0][1] - NT] > iter || tabu_until[N[2][0] - LB][N[2][1] - NT] > iter;
            if (tabu && c >= best) continue;
            if (c < bmc) { bmc = c; bkind = 0; ba = i; bb = j; bpat = pat; ties = 1; }
            else if (c == bmc && rndint(++ties) == 0) { bkind = 0; ba = i; bb = j; bpat = pat; }
        }
        for (int i = 0; i < NR; i++) {
            int l = ORl[i], o = ORo[i];
            for (int k = 0; k < 2; k++) {
                int d = dl[k];
                if (deg[l] != 3 || deg[d] != 2 || has_e(d, o) || has_e(tm[d], tm[o])) continue;
                if (l == d || tm[l] == d) continue;
                int A[2][2] = {{l, o}, {tm[l], tm[o]}}, N[2][2] = {{d, o}, {tm[d], tm[o]}};
                for (int a = 0; a < 2; a++) del_e(A[a][0], A[a][1]);
                for (int a = 0; a < 2; a++) add_e(N[a][0], N[a][1]);
                int c = far_cost();
                for (int a = 0; a < 2; a++) del_e(N[a][0], N[a][1]);
                for (int a = 0; a < 2; a++) add_e(A[a][0], A[a][1]);
                int tabu = tabu_until[d - LB][o - NT] > iter;
                if (tabu && c >= best) continue;
                if (c < bmc) { bmc = c; bkind = 1; ba = i; bb = k; ties = 1; }
                else if (c == bmc && rndint(++ties) == 0) { bkind = 1; ba = i; bb = k; }
            }
        }
        if (bkind < 0) continue;
        int T = tmin + rndint(tmax - tmin + 1);
        if (bkind == 0) {
            int l1 = ORl[ba], o1 = ORo[ba], l2 = ORl[bb], o2 = ORo[bb];
            if (bpat == 1) { l2 = tm[l2]; o2 = tm[o2]; }
            int A[4][2] = {{l1, o1}, {tm[l1], tm[o1]}, {l2, o2}, {tm[l2], tm[o2]}};
            int N[4][2] = {{l1, o2}, {tm[l1], tm[o2]}, {l2, o1}, {tm[l2], tm[o1]}};
            for (int a = 0; a < 4; a++) del_e(A[a][0], A[a][1]);
            for (int a = 0; a < 4; a++) add_e(N[a][0], N[a][1]);
            for (int a = 0; a < 4; a++) tabu_until[A[a][0] - LB][A[a][1] - NT] = iter + T;
        } else {
            int l = ORl[ba], o = ORo[ba], d = dl[bb];
            int A[2][2] = {{l, o}, {tm[l], tm[o]}}, N[2][2] = {{d, o}, {tm[d], tm[o]}};
            for (int a = 0; a < 2; a++) del_e(A[a][0], A[a][1]);
            for (int a = 0; a < 2; a++) add_e(N[a][0], N[a][1]);
            for (int a = 0; a < 2; a++) tabu_until[A[a][0] - LB][A[a][1] - NT] = iter + T;
        }
        recompute_deficits();
        cur = bmc;
        if (cur < best) {
            best = cur; lastImp = iter;
            save_best();
            write_graph(out);
            fprintf(stderr, "iter %ld t=%.1f NEW BEST far=%d (same6=%d)\n", iter, now() - t0, best, same6_cost());
            if (best == 0) break;
        }
        if (iter % 100 == 0) fprintf(stderr, "iter %ld t=%.1f cur=%d best=%d\n", iter, now() - t0, cur, best);
        if (iter - lastImp > pert) {
            load_best();
            recompute_deficits();
            for (int kk = 0; kk < 2; kk++) {
                collect_reps();
                int i = rndint(NR), j = rndint(NR);
                int l1 = ORl[i], o1 = ORo[i], l2 = ORl[j], o2 = ORo[j];
                if (i == j || l1 == l2 || o1 == o2 || has_e(l1, o2) || has_e(l2, o1)) continue;
                if (l1 == tm[l2] || o1 == tm[o2]) continue;
                int A[4][2] = {{l1, o1}, {tm[l1], tm[o1]}, {l2, o2}, {tm[l2], tm[o2]}};
                int N[4][2] = {{l1, o2}, {tm[l1], tm[o2]}, {l2, o1}, {tm[l2], tm[o1]}};
                for (int a = 0; a < 4; a++) del_e(A[a][0], A[a][1]);
                for (int a = 0; a < 4; a++) add_e(N[a][0], N[a][1]);
            }
            recompute_deficits();
            cur = far_cost();
            if (!symmetric_ok()) { fprintf(stderr, "ASYM after perturb\n"); return 1; }
            lastImp = iter;
            fprintf(stderr, "iter %ld restart from best, cur=%d\n", iter, cur);
        }
    }
    fprintf(stderr, "done iters=%ld best=%d time=%.1f\n", iter, best, now() - t0);
    printf("best %d\n", best);
    return 0;
}
