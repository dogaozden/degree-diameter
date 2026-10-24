/* ctrl_lift.c -- C5 of the (16,5) squad: voltage lifts of a small 4-regular bipartite base multigraph B.

   Controller C = lift of B by a group G (|G| = n): base A-vertex a_i, B-vertex b_j, edge k = (a_i, b_j) with voltage
   v_k in G; controller vertices (a_i, g) and (b_j, h); edge (a_i, g) ~ (b_j, v_k g).  m = nb*n vertices per side.
   G acts by right multiplication (automorphisms), so only the base sources (a_i, e) and (b_j, e) need checking.

   Walks: a non-backtracking walk of length 4 in C from (a_i, e) is a base walk k1 k2 k3 k4 with consecutive edges
   distinct; it ends at (a_p, x) with x = v4^-1 v3 v2^-1 v1 (the walk leaves B-vertices by v^-1).  From (b_j, e):
   x = v4 v3^-1 v2 v1^-1.  Cost = number of (base source, same-side target (p, x)) pairs not reached.  Cost 0 is the
   exact-NB-4 property of C (u = v included), which gives diameter <= 5 for the 16-regular route-chart lift.

   Bases: k44 (K_{4,4}, nb = 4, 16 edges), k33m (K_{3,3} + one doubled perfect matching, nb = 3, 12 edges),
   dip4 (1+1 dipole with 4 parallel edges, nb = 1, 4 edges: the Haar case, used as a self-test).
   Spanning tree edges are gauge-fixed to the identity (WLOG); parallel edges must get distinct voltages.

   usage: ctrl_lift TABLE BASE SECONDS SEED [OUT.edges|-] [T0] [FIXED]
     FIXED = comma list of E voltages: no annealing, only evaluate (self-test).
   Prints best_cost and the voltages; writes the controller edge list "a b" of the best assignment to OUT
   (A-vertex (a_i,g) -> i*n+g, B-vertex (b_j,h) -> j*n+h; 4 lines per A-vertex). */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <time.h>
#include <stdint.h>

static uint64_t rs = 88172645463325252ULL;
static inline uint64_t xr(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }

static int n, *T, *Inv, e;
static int nb, E;
static int EA[16], EB[16], istree[16], pairid[16], freel[16], nfree;
static int v[16], vinv[16];
static int nW, (*WK)[4], *WS, *WSLOT;
static unsigned char *cov;
static int ncov;

static inline int mul(int a, int b) { return T[a * n + b]; }
static inline int at_(int side, int k) { return side == 0 ? EA[k] : EB[k]; }
static inline int oth_(int side, int k) { return side == 0 ? EB[k] : EA[k]; }

static void set_base(const char *name) {
    int tree[16], nt = 0;
    E = 0;
    if (!strcmp(name, "k44")) {
        nb = 4;
        for (int i = 0; i < 4; i++) for (int j = 0; j < 4; j++) { EA[E] = i; EB[E] = j; E++; }
        int t[] = {0, 1, 2, 3, 4, 8, 12}; /* a0-b_j and a_i-b0 */
        for (int q = 0; q < 7; q++) tree[nt++] = t[q];
    } else if (!strcmp(name, "k33m")) {
        nb = 3;
        for (int i = 0; i < 3; i++) for (int j = 0; j < 3; j++) { EA[E] = i; EB[E] = j; E++; }
        for (int i = 0; i < 3; i++) { EA[E] = i; EB[E] = i; E++; } /* second copy of the matching edges */
        int t[] = {0, 1, 2, 3, 6};
        for (int q = 0; q < 5; q++) tree[nt++] = t[q];
    } else if (!strcmp(name, "dip4")) {
        nb = 1;
        for (int k = 0; k < 4; k++) { EA[E] = 0; EB[E] = 0; E++; }
        tree[nt++] = 0;
    } else { fprintf(stderr, "unknown base %s\n", name); exit(2); }
    for (int k = 0; k < E; k++) istree[k] = 0;
    for (int q = 0; q < nt; q++) istree[tree[q]] = 1;
    nfree = 0;
    for (int k = 0; k < E; k++) { pairid[k] = EA[k] * nb + EB[k]; if (!istree[k]) freel[nfree++] = k; }
}

/* all NB walks of length 4 from (side s, base vertex src), for both sides */
static void build_walks(void) {
    nW = 2 * nb * 108;
    WK = malloc(sizeof(*WK) * nW); WS = malloc(sizeof(int) * nW); WSLOT = malloc(sizeof(int) * nW);
    int w = 0;
    for (int s = 0; s < 2; s++) for (int src = 0; src < nb; src++)
        for (int k1 = 0; k1 < E; k1++) {
            if (at_(s, k1) != src) continue;
            int i1 = oth_(s, k1), s1 = 1 - s;
            for (int k2 = 0; k2 < E; k2++) {
                if (k2 == k1 || at_(s1, k2) != i1) continue;
                int i2 = oth_(s1, k2), s2 = s;
                for (int k3 = 0; k3 < E; k3++) {
                    if (k3 == k2 || at_(s2, k3) != i2) continue;
                    int i3 = oth_(s2, k3), s3 = s1;
                    for (int k4 = 0; k4 < E; k4++) {
                        if (k4 == k3 || at_(s3, k4) != i3) continue;
                        int p = oth_(s3, k4); /* endpoint on side s (after 4 steps) */
                        if (w >= nW) { fprintf(stderr, "walk overflow\n"); exit(3); }
                        WK[w][0] = k1; WK[w][1] = k2; WK[w][2] = k3; WK[w][3] = k4;
                        WS[w] = s; WSLOT[w] = ((s * nb + src) * nb + p) * n;
                        w++;
                    }
                }
            }
        }
    if (w != nW) { fprintf(stderr, "walk count %d != %d\n", w, nW); exit(3); }
    ncov = 2 * nb * nb * n;
    cov = malloc(ncov);
}

/* uncovered (source, target) pairs */
static int evalcost(void) {
    memset(cov, 0, ncov);
    for (int w = 0; w < nW; w++) {
        int x = e, s = WS[w];
        for (int t = 0; t < 4; t++) {
            int k = WK[w][t];
            int side = (s + t) & 1; /* side we leave at step t */
            x = mul(side == 0 ? v[k] : vinv[k], x);
        }
        cov[WSLOT[w] + x] = 1;
    }
    int c = 0;
    for (int i = 0; i < ncov; i++) c += !cov[i];
    return c;
}

/* voltage w on edge k keeps parallel edges distinct */
static int ok_val(int k, int w) {
    for (int k2 = 0; k2 < E; k2++)
        if (k2 != k && pairid[k2] == pairid[k] && v[k2] == w) return 0;
    return 1;
}

int main(int argc, char **argv) {
    if (argc < 5) { fprintf(stderr, "usage: ctrl_lift TABLE BASE SECONDS SEED [OUT|-] [T0] [FIXED]\n"); return 1; }
    FILE *f = fopen(argv[1], "r");
    if (!f || fscanf(f, "%d", &n) != 1) { fprintf(stderr, "bad table\n"); return 2; }
    T = malloc(sizeof(int) * n * n); Inv = malloc(sizeof(int) * n);
    for (int i = 0; i < n * n; i++) if (fscanf(f, "%d", &T[i]) != 1) { fprintf(stderr, "short table\n"); return 2; }
    fclose(f);
    e = -1;
    for (int i = 0; i < n && e < 0; i++) { int ok = 1; for (int j = 0; j < n; j++) if (T[i * n + j] != j) { ok = 0; break; } if (ok) e = i; }
    if (e < 0) { fprintf(stderr, "no identity\n"); return 2; }
    for (int i = 0; i < n; i++) for (int j = 0; j < n; j++) if (T[i * n + j] == e) Inv[i] = j;

    const char *base = argv[2];
    double secs = atof(argv[3]);
    rs ^= (uint64_t)atoll(argv[4]) * 0x9E3779B97F4A7C15ULL; if (!rs) rs = 1;
    const char *out = (argc > 5 && strcmp(argv[5], "-")) ? argv[5] : NULL;
    double T0 = argc > 6 ? atof(argv[6]) : 4.0, T1 = 0.1;
    const char *fixed = argc > 7 ? argv[7] : NULL;

    set_base(base);
    build_walks();
    int m = nb * n;

    if (fixed) {
        char *buf = strdup(fixed); char *tok = strtok(buf, ",");
        for (int k = 0; k < E && tok; k++) { v[k] = atoi(tok); tok = strtok(NULL, ","); }
        for (int k = 0; k < E; k++) vinv[k] = Inv[v[k]];
        int c = evalcost();
        printf("base=%s n=%d m=%d FIXED cost=%d\n", base, n, m, c);
        if (out) {
            FILE *fo = fopen(out, "w");
            for (int k = 0; k < E; k++) for (int g = 0; g < n; g++)
                fprintf(fo, "%d %d\n", EA[k] * n + g, EB[k] * n + mul(v[k], g));
            fclose(fo);
        }
        return 0;
    }

    for (int k = 0; k < E; k++) if (istree[k]) { v[k] = e; vinv[k] = e; }
    for (int q = 0; q < nfree; q++) {
        int k = freel[q], w;
        do { w = xr() % n; } while (!ok_val(k, w));
        v[k] = w; vinv[k] = Inv[w];
    }
    int c = evalcost(), best = c, bestv[16];
    memcpy(bestv, v, sizeof v);
    clock_t t0 = clock(); long it = 0; double Tc = T0, el = 0;
    while (best > 0) {
        if ((it & 1023) == 0) {
            el = (double)(clock() - t0) / CLOCKS_PER_SEC;
            if (el >= secs) break;
            Tc = T0 * pow(T1 / T0, el / secs);
        }
        it++;
        int k = freel[xr() % nfree], w = xr() % n;
        if (w == v[k] || !ok_val(k, w)) continue;
        int old = v[k];
        v[k] = w; vinv[k] = Inv[w];
        int c2 = evalcost(), d = c2 - c;
        if (d <= 0 || (double)(xr() % 1000000) / 1e6 < exp(-d / Tc)) {
            c = c2;
            if (c < best) { best = c; memcpy(bestv, v, sizeof v); }
        } else { v[k] = old; vinv[k] = Inv[old]; }
    }
    memcpy(v, bestv, sizeof v);
    for (int k = 0; k < E; k++) vinv[k] = Inv[v[k]];
    el = (double)(clock() - t0) / CLOCKS_PER_SEC;
    printf("base=%s n=%d m=%d best_cost=%d iters=%ld secs=%.1f volt=", base, n, m, best, it, el);
    for (int k = 0; k < E; k++) printf("%d%s", bestv[k], k + 1 < E ? "," : "\n");
    if (out) {
        FILE *fo = fopen(out, "w");
        for (int k = 0; k < E; k++) for (int g = 0; g < n; g++)
            fprintf(fo, "%d %d\n", EA[k] * n + g, EB[k] * n + mul(bestv[k], g));
        fclose(fo);
    }
    return 0;
}
