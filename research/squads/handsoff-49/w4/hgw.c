/* hgw.c (w4, handsoff-49): generic lift search for any base with <= 256 vertices (4-regular, simple or multi).
   Walk-bitset evaluator with one bit per base root (W words), D = 9.
   cost = sum over roots u, lift vertices (v,x) of [no walk of length <= 9 from u to v with voltage x] = 2*far/k.
   Usage: hgw BASE GROUP seconds seed T0 OUTPREFIX [INITSOL]   (ILS: best response on each free voltage, restart from best)
     BASE: "b m" then m edges. GROUP: cyc:k or groups.py .bin file (T[x*k+g] = x*g, identity 0).
   Env: WRITE_EDGES=1 writes OUTPREFIX.edges always; otherwise only at cost 0.  Prints RESULT best=... */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>
#include <time.h>
#define MAXB 256
#define MAXE 1024
#define D 9
static int nb, ne, k, W;
static uint16_t *T;
static int inv_[1024];
static int ea[MAXE], eb[MAXE], ev[MAXE], isfree[MAXE];
static int cot[MAXE], ncot;
static int ninc[MAXB], incw[MAXB][8], incg[MAXB][8];
static uint64_t *SA, *SB;
static uint64_t rs = 88172645463325252ULL;
static inline uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static void load_group(const char *spec) {
    if (strncmp(spec, "cyc:", 4) == 0) {
        k = atoi(spec + 4);
        T = malloc(sizeof(uint16_t) * k * k);
        for (int x = 0; x < k; x++) for (int g = 0; g < k; g++) T[x*k+g] = (uint16_t)((x+g) % k);
    } else {
        FILE *f = fopen(spec, "rb"); if (!f) { perror("group"); exit(1); }
        int32_t N; if (fread(&N, 4, 1, f) != 1) exit(1);
        k = N; T = malloc(sizeof(uint16_t) * k * k);
        if (fread(T, 2, (size_t)k*k, f) != (size_t)k*k) { fprintf(stderr, "short group\n"); exit(1); }
        fclose(f);
    }
    for (int g = 0; g < k; g++) for (int h = 0; h < k; h++) if (T[g*k+h] == 0) { inv_[g] = h; break; }
}
static void load_base(const char *path) {
    FILE *f = fopen(path, "r");
    if (!f || fscanf(f, "%d %d", &nb, &ne) != 2) { fprintf(stderr, "bad base\n"); exit(1); }
    if (nb > MAXB || ne > MAXE) { fprintf(stderr, "base too big\n"); exit(1); }
    for (int e = 0; e < ne; e++) if (fscanf(f, "%d %d", &ea[e], &eb[e]) != 2) exit(1);
    fclose(f);
    W = (nb + 63) / 64;
    /* BFS spanning tree from 0 */
    static int adjE[MAXB][8], deg[MAXB], vis[MAXB], q[MAXB], tree[MAXE];
    memset(deg, 0, sizeof deg); memset(vis, 0, sizeof vis); memset(tree, 0, sizeof tree);
    for (int e = 0; e < ne; e++) { adjE[ea[e]][deg[ea[e]]++] = e; adjE[eb[e]][deg[eb[e]]++] = e; }
    int qh = 0, qt = 0; q[qt++] = 0; vis[0] = 1;
    while (qh < qt) {
        int x = q[qh++];
        for (int i = 0; i < deg[x]; i++) {
            int e = adjE[x][i]; int y = (ea[e] == x) ? eb[e] : ea[e];
            if (!vis[y]) { vis[y] = 1; tree[e] = 1; q[qt++] = y; }
        }
    }
    for (int i = 0; i < nb; i++) if (!vis[i]) { fprintf(stderr, "base disconnected\n"); exit(1); }
    ncot = 0;
    for (int e = 0; e < ne; e++) { isfree[e] = !tree[e]; if (!tree[e]) cot[ncot++] = e; }
}
static void build_inc(void) {
    memset(ninc, 0, sizeof ninc);
    for (int e = 0; e < ne; e++) {
        int a = ea[e], b = eb[e], g = ev[e];
        incw[b][ninc[b]] = a; incg[b][ninc[b]] = g; ninc[b]++;
        incw[a][ninc[a]] = b; incg[a][ninc[a]] = inv_[g]; ninc[a]++;
    }
}
#define IDX(v, x) (((size_t)(v) * k + (x)) * W)
static int eval_cost(void) {
    build_inc();
    size_t sz = (size_t)nb * k * W;
    memset(SA, 0, sz * sizeof(uint64_t));
    for (int v = 0; v < nb; v++) SA[IDX(v, 0) + (v >> 6)] |= 1ULL << (v & 63);
    uint64_t *cur = SA, *nxt = SB;
    for (int step = 1; step <= D; step++) {
        memcpy(nxt, cur, sz * sizeof(uint64_t));
        for (int v = 0; v < nb; v++)
            for (int i = 0; i < ninc[v]; i++) {
                int w = incw[v][i], g = incg[v][i];
                for (int x = 0; x < k; x++) {
                    uint64_t *dst = nxt + IDX(v, T[x*k+g]);
                    const uint64_t *src = cur + IDX(w, x);
                    for (int j = 0; j < W; j++) dst[j] |= src[j];
                }
            }
        uint64_t *t = cur; cur = nxt; nxt = t;
    }
    int cost = 0;
    for (int v = 0; v < nb; v++)
        for (int x = 0; x < k; x++) {
            int c = 0; const uint64_t *p = cur + IDX(v, x);
            for (int j = 0; j < W; j++) c += __builtin_popcountll(p[j]);
            cost += nb - c;
        }
    return cost;
}
int main(int argc, char **argv) {
    if (argc < 7) { fprintf(stderr, "usage: hgw BASE GROUP seconds seed T0 OUTPREFIX [INITSOL]\n"); return 1; }
    load_base(argv[1]);
    load_group(argv[2]);
    double secs = atof(argv[3]);
    rs ^= (uint64_t)atoll(argv[4]) * 0x9E3779B97F4A7C15ULL; if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();
    const char *outp = argv[6];
    SA = malloc(sizeof(uint64_t) * (size_t)nb * k * W);
    SB = malloc(sizeof(uint64_t) * (size_t)nb * k * W);
    for (int e = 0; e < ne; e++) ev[e] = isfree[e] ? (int)(rnd() % k) : 0;
    if (argc > 7) {
        FILE *f = fopen(argv[7], "r"); int e, g;
        while (f && fscanf(f, "%d %d", &e, &g) == 2) ev[e] = g;
        if (f) fclose(f);
    }
    int cur = eval_cost(), best = cur;
    int bestv[MAXE]; memcpy(bestv, ev, sizeof(int) * ne);
    fprintf(stderr, "base b=%d m=%d k=%d n=%d free=%d start cost %d\n", nb, ne, k, nb*k, ncot, cur);
    clock_t tt = clock(); long sweeps = 0, evals = 0;
    int order[MAXE];
    while (ncot > 0 && best > 0) {
        double el = (double)(clock() - tt) / CLOCKS_PER_SEC;
        if (el >= secs) break;
        sweeps++;
        for (int i = 0; i < ncot; i++) order[i] = cot[i];
        for (int i = ncot - 1; i > 0; i--) { int j = (int)(rnd() % (i + 1)); int t = order[i]; order[i] = order[j]; order[j] = t; }
        int improved = 0, cur2 = cur;
        for (int ii = 0; ii < ncot && best > 0; ii++) {
            int e = order[ii];
            int old = ev[e], bv = old, bc = cur2, nties = 1;
            for (int g = 0; g < k; g++) {
                if (g == old) continue;
                ev[e] = g;
                int c = eval_cost(); evals++;
                if (c < bc) { bc = c; bv = g; nties = 1; }
                else if (c == bc && c < cur2) { if (rnd() % (++nties) == 0) bv = g; }
            }
            ev[e] = bv;
            if (bc < cur2) improved = 1;
            cur2 = bc;
            if (cur2 < best) { best = cur2; memcpy(bestv, ev, sizeof(int) * ne); fprintf(stderr, "best %d sweep %ld t=%.0f\n", best, sweeps, el); }
        }
        cur = cur2;
        if (!improved) {
            memcpy(ev, bestv, sizeof(int) * ne);
            for (int r = 0; r < 2 + (int)(rnd() % 3); r++) { int e = cot[rnd() % ncot]; ev[e] = (int)(rnd() % k); }
            cur = eval_cost();
        }
    }
    memcpy(ev, bestv, sizeof(int) * ne);
    int chk = eval_cost();
    char path[512];
    snprintf(path, sizeof path, "%s.best", outp);
    FILE *f = fopen(path, "w"); for (int e = 0; e < ne; e++) fprintf(f, "%d %d\n", e, ev[e]); fclose(f);
    if (chk == 0 || getenv("WRITE_EDGES")) {
        snprintf(path, sizeof path, "%s.edges", outp);
        FILE *g2 = fopen(path, "w");
        fprintf(g2, "%d\n", nb * k);
        for (int e = 0; e < ne; e++) for (int x = 0; x < k; x++)
            fprintf(g2, "%d %d\n", ea[e] * k + x, eb[e] * k + T[x * k + ev[e]]);
        fclose(g2);
    }
    printf("RESULT best=%d k=%d n=%d sweeps=%ld evals=%ld check=%d\n", best, k, nb * k, sweeps, evals, chk);
    return 0;
}
