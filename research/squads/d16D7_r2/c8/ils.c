/* ils.c: ARW-style iterated local search for maximum independent set (perturb by forcing one or more
   non-solution vertices in, local search with (1,2)-swaps and free-vertex insertion, ARW acceptance with
   journal rollback). Graph file: "M E" then per vertex "idx rep deg nbrs...".
   usage: ils GRAPH OUT CPU_SECONDS SEED [INIT_FILE] [TARGET]
   OUT receives the best solution (one vertex index per line) every time it improves. CPU budget via clock(). */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

static int n, *deg, *adjs, *adj;          /* CSR adjacency */
static uint64_t *bm; static int wpr;     /* bit matrix rows */
static char *inS; static int *tight; static long long *sumS;
static int *sol, *pos, nsol;
static int *freeq, nfree, *chkq, nchk;
static int *jv; static char *jo; static long long njour; static int journaling = 1;
static long long *age;
static uint64_t rs;
static inline uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static inline int rndi(int k) { return (int)(rnd() % (uint64_t)k); }
static inline int isadj(int a, int b) { return (bm[(size_t)a * wpr + (b >> 6)] >> (b & 63)) & 1ULL; }
static long long iter = 0;

static void jpush(int v, char op) { if (journaling) { jv[njour] = v; jo[njour] = op; njour++; } }

static void add(int v) {
    inS[v] = 1; pos[v] = nsol; sol[nsol++] = v; age[v] = iter; jpush(v, 1);
    for (int k = adjs[v]; k < adjs[v + 1]; k++) {
        int u = adj[k];
        tight[u]++; sumS[u] += v;
        if (!inS[u] && tight[u] == 1) { chkq[nchk++] = v; }
    }
}
static void rem(int v) {
    inS[v] = 0; int p = pos[v]; int last = sol[--nsol]; sol[p] = last; pos[last] = p; age[v] = iter; jpush(v, -1);
    for (int k = adjs[v]; k < adjs[v + 1]; k++) {
        int u = adj[k];
        tight[u]--; sumS[u] -= v;
        if (!inS[u]) {
            if (tight[u] == 0) freeq[nfree++] = u;
            else if (tight[u] == 1) chkq[nchk++] = (int)sumS[u];
        }
    }
}
static int lbuf[100000];
static int try_swap(int x) {
    int nl = 0;
    for (int k = adjs[x]; k < adjs[x + 1]; k++) {
        int u = adj[k];
        if (!inS[u] && tight[u] == 1) lbuf[nl++] = u;
    }
    if (nl < 2) return 0;
    /* random start to diversify */
    int off = rndi(nl);
    for (int ii = 0; ii < nl; ii++) {
        int a = lbuf[(ii + off) % nl];
        for (int jj = ii + 1; jj < nl; jj++) {
            int b = lbuf[(jj + off) % nl];
            if (!isadj(a, b)) {
                rem(x); add(a); add(b);
                return 1;
            }
        }
    }
    return 0;
}
static void local_search(void) {
    for (;;) {
        while (nfree > 0) {
            int u = freeq[--nfree];
            if (!inS[u] && tight[u] == 0) add(u);
        }
        if (nchk == 0) break;
        int x = chkq[--nchk];
        if (inS[x]) {
            if (try_swap(x)) continue;
        }
    }
}
static void rollback(void) {
    journaling = 0;
    for (long long k = njour - 1; k >= 0; k--) {
        if (jo[k] == 1) rem(jv[k]); else add(jv[k]);
    }
    journaling = 1; njour = 0; nfree = 0; nchk = 0;
}
static void write_sol(const char *fn, int *s, int ns) {
    FILE *f = fopen(fn, "w");
    for (int i = 0; i < ns; i++) fprintf(f, "%d\n", s[i]);
    fclose(f);
}
int main(int argc, char **argv) {
    if (argc < 5) { fprintf(stderr, "usage: ils GRAPH OUT CPU SEED [INIT] [TARGET]\n"); return 1; }
    double budget = atof(argv[3]);
    rs = 0x2545F4914F6CDD1DULL ^ ((uint64_t)atoll(argv[4]) * 0x9E3779B97F4A7C15ULL); if (!rs) rs = 1;
    FILE *f = fopen(argv[1], "r");
    int M, E; if (fscanf(f, "%d %d", &M, &E) != 2) return 1;
    n = M;
    deg = calloc(n, sizeof(int)); int **nb = malloc(sizeof(int *) * n);
    for (int i = 0; i < n; i++) {
        int idx, rep, d; if (fscanf(f, "%d %d %d", &idx, &rep, &d) != 3) return 1;
        nb[idx] = malloc(sizeof(int) * (d + 1)); deg[idx] = d;
        for (int k = 0; k < d; k++) if (fscanf(f, "%d", &nb[idx][k]) != 1) return 1;
    }
    fclose(f);
    adjs = malloc(sizeof(int) * (n + 1)); adjs[0] = 0;
    for (int i = 0; i < n; i++) adjs[i + 1] = adjs[i] + deg[i];
    adj = malloc(sizeof(int) * adjs[n]);
    wpr = (n + 63) / 64;
    bm = calloc((size_t)n * wpr, sizeof(uint64_t));
    for (int i = 0; i < n; i++) for (int k = 0; k < deg[i]; k++) {
        int u = nb[i][k]; adj[adjs[i] + k] = u;
        bm[(size_t)i * wpr + (u >> 6)] |= 1ULL << (u & 63);
    }
    inS = calloc(n, 1); tight = calloc(n, sizeof(int)); sumS = calloc(n, sizeof(long long));
    sol = malloc(sizeof(int) * n); pos = malloc(sizeof(int) * n); nsol = 0;
    freeq = malloc(sizeof(int) * (size_t)(n * 200 + 16)); nfree = 0;
    chkq = malloc(sizeof(int) * (size_t)(n * 200 + 16)); nchk = 0;
    jv = malloc(sizeof(int) * (size_t)(n * 1000 + 16)); jo = malloc((size_t)(n * 1000 + 16));
    age = calloc(n, sizeof(long long));
    /* initial solution */
    if (argc > 5 && strcmp(argv[5], "-") != 0) {
        FILE *g = fopen(argv[5], "r"); int v;
        while (g && fscanf(g, "%d", &v) == 1) {
            if (v >= 0 && v < n && !inS[v] && tight[v] == 0) add(v);
        }
        if (g) fclose(g);
    }
    int target = argc > 6 ? atoi(argv[6]) : 1 << 30;
    /* greedy fill (min-degree style random) */
    for (int v = 0; v < n; v++) if (!inS[v] && tight[v] == 0) add(v);
    local_search();
    njour = 0;
    int best = nsol; int *bsol = malloc(sizeof(int) * n); memcpy(bsol, sol, sizeof(int) * nsol);
    int cur = nsol;
    write_sol(argv[2], bsol, best);
    printf("init %d\n", best); fflush(stdout);
    double t0 = (double)clock() / CLOCKS_PER_SEC;
    long long last_imp = 0; long long nimp = 0;
    for (iter = 1;; iter++) {
        if ((iter & 255) == 0) {
            double el = (double)clock() / CLOCKS_PER_SEC - t0;
            if (el > budget || best >= target) break;
        }
        njour = 0;
        /* perturbation: force k vertices in */
        int k = 1;
        if (rndi(2 * (cur + 1)) == 0) { k = 2; while (rndi(2) == 0 && k < 8) k++; }
        for (int t = 0; t < k; t++) {
            int bestv = -1; long long ba = 0;
            for (int c = 0; c < 4; c++) {
                int v = rndi(n);
                if (inS[v]) continue;
                if (bestv < 0 || age[v] < ba) { bestv = v; ba = age[v]; }
            }
            if (bestv < 0) continue;
            int v = bestv;
            for (int kk = adjs[v]; kk < adjs[v + 1]; kk++) if (inS[adj[kk]]) rem(adj[kk]);
            if (!inS[v] && tight[v] == 0) add(v);
        }
        local_search();
        int s = nsol;
        if (s > best) {
            best = s; memcpy(bsol, sol, sizeof(int) * nsol); write_sol(argv[2], bsol, best);
            nimp++; last_imp = iter;
            double el = (double)clock() / CLOCKS_PER_SEC - t0;
            printf("best %d iter %lld t %.1f\n", best, iter, el); fflush(stdout);
        }
        if (s >= cur) { cur = s; njour = 0; }
        else {
            int delta = cur - s, dstar = best - s;
            double pacc = 1.0 / (1.0 + (double)delta * (double)dstar);
            if ((double)(rnd() % 1000000) / 1000000.0 < pacc) { cur = s; njour = 0; }
            else { rollback(); }
        }
        if (iter - last_imp > 2000000 && cur < best) {
            /* restart from best */
            rollback(); njour = 0;
            /* rebuild from best */
            while (nsol > 0) rem(sol[nsol - 1]);
            njour = 0; nfree = 0; nchk = 0;
            for (int i = 0; i < best; i++) if (!inS[bsol[i]] && tight[bsol[i]] == 0) add(bsol[i]);
            cur = nsol; njour = 0; last_imp = iter;
        }
    }
    double el = (double)clock() / CLOCKS_PER_SEC - t0;
    printf("final best %d iters %lld cpu %.1f improvements %lld\n", best, iter, el, nimp);
    return 0;
}
