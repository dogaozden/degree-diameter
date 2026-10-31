/* lift2.c (r2c): polarity covers of a base with stub items, Z_t-symmetric M, optional fixed vertex.
   M vertices: (u,x) = u*t + x for u < k, x in Z_t; if H, fixed vertex F = k*t (m = k*t + H).
   Items (each base vertex has 3 stubs; fibre vertex (u,x) has M-degree 3):
     type 0 edge (u<v, g): M[(u,x),(v,x+g)] = 1 for all x (and symmetric). 1 stub at u, 1 at v.
     type 1 loop (u, g):   if 2g % t != 0: M[(u,x),(u,x+-g)] = 1 (2 stubs);
                           if 2g % t == 0: M[(u,x),(u,x+g)] = 1 (1 stub; g = 0 is an M-loop).
     hub (H=1, t=3): orbit hu joined to F: M[(hu,x),F] = 1 for all x (1 stub at hu).
   cost = number of unordered pairs {i,j} of M with no even walk of length <= 6 (far of cover = 2*cost).
   Cover written as edge list (A_i = i, B_j = m + j), checked with bin/score37 by the caller.
   Usage: lift2 k t H seed seconds T0 T1 iters outprefix [pert Tr0 Tr1]
*/
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>
#include <time.h>
#define MAXM 128
#define MAXI 200

typedef struct { int type, u, v, g; } Item;
static int k, t, H, m, F;
static Item it[MAXI];
static int NI, hu;
static uint64_t adj[MAXM][2];
static uint64_t rs = 88172645463325252ULL;
static inline uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static inline int rndi(int n) { return (int)(rnd() % (uint64_t)n); }
static inline double rndu(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }
static double now(void) { struct timespec ts; clock_gettime(CLOCK_MONOTONIC, &ts); return ts.tv_sec + 1e-9 * ts.tv_nsec; }
static inline int getadj(int i, int j) { return (adj[i][j >> 6] >> (j & 63)) & 1; }

static int nrm(int g) { g %= t; if (g < 0) g += t; if ((2 * g) % t == 0) return g; return g <= t - g ? g : t - g; }
static int stub1(int g) { return (2 * g) % t == 0; }
static Item mk_edge(int a, int b, int g) {
    Item x; x.type = 0; g %= t; if (g < 0) g += t;
    if (a < b) { x.u = a; x.v = b; x.g = g; } else { x.u = b; x.v = a; x.g = (t - g) % t; }
    return x;
}
static Item mk_loop(int u, int g) { Item x; x.type = 1; x.u = u; x.v = u; x.g = nrm(g); return x; }

static int dup_with(int idx) {
    Item *a = &it[idx];
    for (int j = 0; j < NI; j++) {
        if (j == idx) continue;
        Item *b = &it[j];
        if (a->type == 0 && b->type == 0 && a->u == b->u && a->v == b->v && a->g == b->g) return 1;
        if (a->type == 1 && b->type == 1 && a->u == b->u && a->g == b->g) return 1;
    }
    return 0;
}
static inline void setb(int a, int b) { adj[a][b >> 6] |= 1ULL << (b & 63); }
static void rebuild(void) {
    memset(adj, 0, sizeof adj);
    for (int i = 0; i < NI; i++) {
        Item *x = &it[i];
        if (x->type == 0) for (int y = 0; y < t; y++) { int a = x->u * t + y, b = x->v * t + (y + x->g) % t; setb(a, b); setb(b, a); }
        else for (int y = 0; y < t; y++) { int a = x->u * t + y, b = x->u * t + (y + x->g) % t; setb(a, b); setb(b, a); }
    }
    if (H) for (int y = 0; y < t; y++) { int a = hu * t + y; setb(a, F); setb(F, a); }
}
static int deg_ok(void) {
    for (int a = 0; a < m; a++) if (__builtin_popcountll(adj[a][0]) + __builtin_popcountll(adj[a][1]) != 3) return 0;
    return 1;
}
/* base stub check (independent of M): each base vertex has exactly 3 stubs */
static int stubs_ok(void) {
    int s[MAXM] = {0};
    for (int i = 0; i < NI; i++) {
        Item *x = &it[i];
        if (x->type == 0) { s[x->u]++; s[x->v]++; }
        else s[x->u] += stub1(x->g) ? 1 : 2;
    }
    if (H) s[hu]++;
    for (int u = 0; u < k; u++) if (s[u] != 3) return 0;
    return 1;
}

/* ---- cost: unordered pairs {i,j} with no even walk of length <= 6 (bitset H-balls, as in c6/lift.c) ---- */
static uint64_t Bw[MAXM][2], H2[MAXM][2];
static int cost_full(void) {
    int j, i, w;
    for (j = 0; j < m; j++) {
        uint64_t r0 = 0, r1 = 0;
        for (w = 0; w < 2; w++) {
            uint64_t x = adj[j][w];
            while (x) { int tt = __builtin_ctzll(x); x &= x - 1; int kk = w * 64 + tt; r0 |= adj[kk][0]; r1 |= adj[kk][1]; }
        }
        Bw[j][0] = r0; Bw[j][1] = r1;
    }
    for (j = 0; j < m; j++) {
        uint64_t r0 = 0, r1 = 0;
        for (w = 0; w < 2; w++) {
            uint64_t x = Bw[j][w];
            while (x) { int tt = __builtin_ctzll(x); x &= x - 1; int kk = w * 64 + tt; r0 |= Bw[kk][0]; r1 |= Bw[kk][1]; }
        }
        H2[j][0] = r0; H2[j][1] = r1;
    }
    long total = 0;
    for (i = 0; i < m; i++) {
        uint64_t r0 = 0, r1 = 0;
        for (w = 0; w < 2; w++) {
            uint64_t x = Bw[i][w];
            while (x) { int tt = __builtin_ctzll(x); x &= x - 1; int kk = w * 64 + tt; r0 |= H2[kk][0]; r1 |= H2[kk][1]; }
        }
        int cov = __builtin_popcountll(r0) + __builtin_popcountll(r1);
        total += m - cov;
    }
    return (int)(total / 2);
}

static void write_cover(const char *fn) {
    FILE *f = fopen(fn, "w");
    if (!f) { perror(fn); return; }
    fprintf(f, "%d\n", 2 * m);
    for (int i = 0; i < m; i++) for (int j = 0; j < m; j++) if (getadj(i, j)) fprintf(f, "%d %d\n", i, m + j);
    fclose(f);
}
static void write_items(const char *fn, int cost) {
    FILE *f = fopen(fn, "w");
    if (!f) return;
    fprintf(f, "# k=%d t=%d H=%d hu=%d m=%d cost=%d far=%d\n", k, t, H, hu, m, cost, 2 * cost);
    for (int i = 0; i < NI; i++) fprintf(f, "%d %d %d %d\n", it[i].type, it[i].u, it[i].v, it[i].g);
    fclose(f);
}

/* ---- random initial base: configuration model over the stubs, parity fixed by one zero loop ---- */
static void random_init(void) {
    for (;;) {
        NI = 0;
        hu = H ? rndi(k) : -1;
        int s[MAXM];
        for (int u = 0; u < k; u++) s[u] = 3 - (u == hu);
        int tot = 0; for (int u = 0; u < k; u++) tot += s[u];
        if (tot & 1) { int u; do u = rndi(k); while (s[u] < 1); it[NI++] = mk_loop(u, 0); s[u]--; }
        int stubs[3 * MAXM], ns = 0;
        for (int u = 0; u < k; u++) for (int c = 0; c < s[u]; c++) stubs[ns++] = u;
        int tries = 0;
        while (ns > 0 && tries < 20000) {
            tries++;
            int p = rndi(ns), q = rndi(ns);
            if (p == q) continue;
            int a = stubs[p], b = stubs[q];
            if (a == b) continue;
            if (NI >= MAXI - 1) break;
            it[NI] = mk_edge(a, b, rndi(t)); NI++;
            if (dup_with(NI - 1)) { NI--; continue; }
            int hi = p > q ? p : q, lo = p > q ? q : p;
            stubs[hi] = stubs[ns - 1]; ns--;
            stubs[lo] = stubs[ns - 1]; ns--;
        }
        if (ns == 0) break;
    }
}

/* ---- stub-preserving moves; each returns 1 if applied (state valid), 0 otherwise (caller restores) ---- */
static int mv_volt(void) {
    int i = rndi(NI); Item *x = &it[i];
    if (x->type == 0) {
        int g2 = rndi(t); if (g2 == x->g) return 0;
        x->g = g2; return !dup_with(i);
    }
    if (stub1(x->g) || t < 3) return 0;
    int g2 = nrm(rndi(t)); if (stub1(g2) || g2 == x->g) return 0;
    x->g = g2; return !dup_with(i);
}
static int mv_switch(void) {
    int i = rndi(NI), j = rndi(NI);
    if (i == j || it[i].type || it[j].type) return 0;
    int a = it[i].u, b = it[i].v, c = it[j].u, d = it[j].v;
    if (rnd() & 1) { int tt = c; c = d; d = tt; }
    if (a == c || b == d) return 0;
    it[i] = mk_edge(a, c, rndi(t)); it[j] = mk_edge(b, d, rndi(t));
    return !dup_with(i) && !dup_with(j);
}
static int mv_split(void) {  /* 2-stub loop (u,g) + edge (c,d) -> edges (u,c), (u,d) */
    int p = rndi(NI), j = rndi(NI);
    if (p == j || it[p].type != 1 || stub1(it[p].g) || it[j].type != 0) return 0;
    int u = it[p].u, c = it[j].u, d = it[j].v;
    if (u == c || u == d) return 0;
    it[p] = mk_edge(u, c, rndi(t)); it[j] = mk_edge(u, d, rndi(t));
    return !dup_with(p) && !dup_with(j);
}
static int mv_combine(void) { /* edges (u,c), (u,d) -> 2-stub loop (u,g) + edge (c,d) */
    if (t < 3) return 0;
    int i = rndi(NI), j = rndi(NI);
    if (i == j || it[i].type || it[j].type) return 0;
    int u = (rnd() & 1) ? it[i].u : it[i].v;
    if (it[j].u != u && it[j].v != u) return 0;
    int c = (it[i].u == u) ? it[i].v : it[i].u;
    int d = (it[j].u == u) ? it[j].v : it[j].u;
    if (c == d) return 0;
    int g2; do g2 = nrm(rndi(t)); while (stub1(g2));
    it[i] = mk_loop(u, g2); it[j] = mk_edge(c, d, rndi(t));
    return !dup_with(i) && !dup_with(j);
}
static int mv_zs(void) { /* 1-stub loop at a + edge (c,d) -> edge (a,c) + 1-stub loop at d */
    int p = rndi(NI), j = rndi(NI);
    if (p == j || it[p].type != 1 || !stub1(it[p].g) || it[j].type != 0) return 0;
    int a = it[p].u, c = it[j].u, d = it[j].v;
    if (rnd() & 1) { int tt = c; c = d; d = tt; }
    if (a == c || a == d) return 0;
    int g1 = (t % 2 == 0 && (rnd() & 1)) ? t / 2 : 0;
    it[p] = mk_edge(a, c, rndi(t)); it[j] = mk_loop(d, g1);
    return !dup_with(p) && !dup_with(j);
}

static int mv_pairloops(void) { /* 1-stub loops at a, b -> edge (a,b) */
    int p = rndi(NI), q = rndi(NI);
    if (p == q || it[p].type != 1 || it[q].type != 1 || !stub1(it[p].g) || !stub1(it[q].g)) return 0;
    int a = it[p].u, b = it[q].u;
    if (a == b) return 0;
    int pi = p;
    it[p] = mk_edge(a, b, rndi(t));
    if (q == NI - 1) NI--;
    else { it[q] = it[NI - 1]; NI--; if (pi == NI) pi = q; }
    return !dup_with(pi);
}
static int mv_unpair(void) { /* edge (a,b) -> 1-stub loops at a and b */
    int j = rndi(NI);
    if (it[j].type != 0 || NI >= MAXI - 1) return 0;
    int a = it[j].u, b = it[j].v;
    int g1 = (t % 2 == 0 && (rnd() & 1)) ? t / 2 : 0;
    it[j] = mk_loop(a, 0);
    it[NI++] = mk_loop(b, g1);
    return !dup_with(j) && !dup_with(NI - 1);
}
static int mv_hub(void) {
    if (!H) return 0;
    if (rnd() & 1) { /* hub at u, edge (c,d) -> hub at c, edge (u,d) */
        int j = rndi(NI); if (it[j].type) return 0;
        int c = it[j].u, d = it[j].v; if (rnd() & 1) { int tt = c; c = d; d = tt; }
        if (hu == c || hu == d) return 0;
        it[j] = mk_edge(hu, d, rndi(t)); hu = c;
        return !dup_with(j);
    } else { /* hub at u, 1-stub loop at c -> hub at c, 1-stub loop at u */
        int p = rndi(NI); if (it[p].type != 1 || !stub1(it[p].g)) return 0;
        int c = it[p].u; if (c == hu) return 0;
        int g1 = (t % 2 == 0 && (rnd() & 1)) ? t / 2 : 0;
        it[p] = mk_loop(hu, g1); hu = c;
        return !dup_with(p);
    }
}
static int apply_move(void) {
    double r = rndu(); int ok;
    if (r < 0.20) ok = mv_volt();
    else if (r < 0.50) ok = mv_switch();
    else if (r < 0.60) ok = mv_split();
    else if (r < 0.70) ok = mv_combine();
    else if (r < 0.78) ok = mv_zs();
    else if (r < 0.84) ok = mv_pairloops();
    else if (r < 0.90) ok = mv_unpair();
    else ok = mv_hub();
    return ok;
}

int main(int argc, char **argv) {
    if (argc < 10) { fprintf(stderr, "usage: lift2 k t H seed seconds T0 T1 iters outprefix [pert Tr0 Tr1]\n"); return 2; }
    k = atoi(argv[1]); t = atoi(argv[2]); H = atoi(argv[3]);
    m = k * t + H; F = k * t;
    if (m > MAXM) { fprintf(stderr, "m too big\n"); return 2; }
    if (H && t != 3) { fprintf(stderr, "hub needs t=3\n"); return 2; }
    rs ^= (uint64_t)atoll(argv[4]) * 0x9E3779B97F4A7C15ULL; for (int i = 0; i < 10; i++) rnd();
    double tlim = atof(argv[5]), T0 = atof(argv[6]), T1 = atof(argv[7]);
    long iters = atol(argv[8]);
    const char *outp = argv[9];
    int pert = argc > 10 ? atoi(argv[10]) : 0;
    double Tr0 = argc > 11 ? atof(argv[11]) : T0, Tr1 = argc > 12 ? atof(argv[12]) : T1;
    double t0 = now();
    int gbest = 1 << 30, gNI = 0, ghu = -1; Item gIt[MAXI];
    int havebest = 0;
    char fn[512];
    long total = 0, acc = 0; int restart = 0;
    Item sv[MAXI]; int svNI, svhu;
    printf("lift2 k=%d t=%d H=%d m=%d n=%d\n", k, t, H, m, 2 * m); fflush(stdout);
    while (now() - t0 < tlim) {
        restart++;
        double A0 = T0, A1 = T1;
        if (pert > 0 && havebest && restart > 1) {
            NI = gNI; hu = ghu; memcpy(it, gIt, sizeof(Item) * NI);
            for (int p = 0, done = 0; done < pert && p < 100000; p++) { if (apply_move()) done++; }
            A0 = Tr0; A1 = Tr1;
        } else random_init();
        rebuild();
        int cur = cost_full(), rbest = cur;
        double lt0 = log(A0), lt1 = log(A1);
        Item rIt[MAXI]; int rNI = NI, rhu = hu; memcpy(rIt, it, sizeof(Item) * NI);
        for (long s = 0; s < iters; s++) {
            double T = exp(lt0 + (lt1 - lt0) * (double)s / (double)iters);
            svNI = NI; svhu = hu; memcpy(sv, it, sizeof(Item) * NI);
            if (!apply_move()) { NI = svNI; hu = svhu; memcpy(it, sv, sizeof(Item) * NI); continue; }
            total++;
            rebuild();
            int nc = cost_full();
            int d = nc - cur;
            if (d <= 0 || rndu() < exp(-d / T)) {
                acc++;
                cur = nc;
                if (cur < rbest) { rbest = cur; rNI = NI; rhu = hu; memcpy(rIt, it, sizeof(Item) * NI); }
                if (cur < gbest) {
                    gbest = cur; havebest = 1; gNI = NI; ghu = hu; memcpy(gIt, it, sizeof(Item) * NI);
                    snprintf(fn, sizeof fn, "%s_best.edges", outp); write_cover(fn);
                    snprintf(fn, sizeof fn, "%s_best.items", outp); write_items(fn, gbest);
                    printf("  new best cost=%d far=%d it=%ld t=%.1f degok=%d stubok=%d\n", gbest, 2 * gbest, total, now() - t0, deg_ok(), stubs_ok()); fflush(stdout);
                    if (gbest == 0) { printf("ZERO COST m=%d k=%d t=%d H=%d\n", m, k, t, H); goto done; }
                }
            } else {
                NI = svNI; hu = svhu; memcpy(it, sv, sizeof(Item) * NI);
                rebuild();
            }
        }
        printf("restart %d rbest=%d cur=%d gbest=%d moves=%ld acc=%ld rate=%.0f/s t=%.0f\n", restart, rbest, cur, gbest, total, acc, total / (now() - t0), now() - t0);
        fflush(stdout);
        (void)rIt; (void)rNI; (void)rhu;
    }
done:
    printf("FINAL k=%d t=%d H=%d m=%d best cost=%d far=%d\n", k, t, H, m, gbest, 2 * gbest);
    return 0;
}
