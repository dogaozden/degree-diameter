/* omega_model.h (table-audit, omega/): Gomez's compound Omega B_1 (thesis UPC 1986, sec. 2.9.3, Fig. 2.21 a/b) with an
   ARBITRARY labelling of every copy.  B_1 = H(q) incidence graph from tools/moore_build.c (points 0..n-1, lines n..2n-1).
   alpha blocks of 5 copies (copy c = 5B + i, i in Z_5), block type a or b, and per block the class used as "inner"
   (L: lines, P: points).  Rows t in [n].  Copy c marks one point P_c[t] and one line L_c[t] per row t (P_c, L_c
   bijections); I_c(t) = the inner-class one, O_c(t) = the other.  Hubs (t,k), (t,kbar), k in Z_5:
     type a: (t,k) ~ I_{5B+k-1}(t), I_{5B+k+1}(t);   (t,kbar) ~ O_{5B+k+2}(t), O_{5B+k+3}(t)
     type b: (t,k) ~ O_{5B+k+3}(t), O_{5B+k+4}(t);   (t,kbar) ~ I_{5B+k-1}(t), I_{5B+k+1}(t)
   (the figure; the thesis's own labelling is P_c[t] = t, L_c[t] = sigma(t) for every c).  Vertex ids: copy vertex
   c*2n + v; hub (t, bar, k) = 5*alpha*2n + 10t + 5bar + k (the same ids as research/d12D8/omega/omega.c).
   Every copy vertex gets +2, every hub has degree 2*alpha; bipartite for any labelling and any inner classes. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

typedef struct {
    int q, n, A, C;            /* n points = n lines, A blocks, C = 5A copies */
    int deg1, nb_m;            /* base degree q+1, number of base edges */
    int *badj;                 /* base adjacency: v*(q+1)+j, v in [0,2n) */
    char types[64], inner[64]; /* per block */
    int *P, *L;                /* P[c*n+t] point index, L[c*n+t] line index (0..n-1) */
    long NV, base;             /* vertices, first hub id */
    int maxd;                  /* max degree */
    int *adj, *deg;            /* graph: adj[v*maxd + j] */
} Omega;

static int om_load_hex(Omega *o, const char *path) {
    FILE *f = fopen(path, "r"); if (!f) { perror(path); return -1; }
    int nv; if (fscanf(f, "%d", &nv) != 1) return -1;
    o->n = nv / 2; int *cnt = calloc(nv, sizeof(int)); int u, v, m = 0;
    int cap = 64; o->badj = malloc(sizeof(int) * (long)nv * cap);
    while (fscanf(f, "%d %d", &u, &v) == 2) { o->badj[(long)u * cap + cnt[u]++] = v; o->badj[(long)v * cap + cnt[v]++] = u; m++; }
    fclose(f); o->deg1 = cnt[0]; o->nb_m = m;
    for (int i = 0; i < nv; i++) if (cnt[i] != o->deg1) { fprintf(stderr, "base not regular\n"); return -1; }
    int *b2 = malloc(sizeof(int) * (long)nv * o->deg1);
    for (int i = 0; i < nv; i++) for (int j = 0; j < o->deg1; j++) b2[(long)i * o->deg1 + j] = o->badj[(long)i * cap + j];
    free(o->badj); o->badj = b2; o->q = o->deg1 - 1; free(cnt); return 0;
}
static void om_alloc(Omega *o, const char *types, const char *inner) {
    strcpy(o->types, types); o->A = strlen(types); o->C = 5 * o->A;
    if (inner && strlen(inner) == (size_t)o->A) strcpy(o->inner, inner); else { for (int B = 0; B < o->A; B++) o->inner[B] = 'L'; o->inner[o->A] = 0; }
    o->P = malloc(sizeof(int) * (long)o->C * o->n); o->L = malloc(sizeof(int) * (long)o->C * o->n);
    for (long i = 0; i < (long)o->C * o->n; i++) { o->P[i] = i % o->n; o->L[i] = i % o->n; }
    o->base = (long)o->C * 2 * o->n; o->NV = o->base + 10L * o->n; o->maxd = o->deg1 + 2 > 2 * o->A ? o->deg1 + 2 : 2 * o->A;
    o->adj = malloc(sizeof(int) * o->NV * o->maxd); o->deg = malloc(sizeof(int) * o->NV);
}
static inline long om_inner(const Omega *o, int c, int t) { int B = c / 5; long off = (long)c * 2 * o->n;
    return o->inner[B] == 'L' ? off + o->n + o->L[(long)c * o->n + t] : off + o->P[(long)c * o->n + t]; }
static inline long om_outer(const Omega *o, int c, int t) { int B = c / 5; long off = (long)c * 2 * o->n;
    return o->inner[B] == 'L' ? off + o->P[(long)c * o->n + t] : off + o->n + o->L[(long)c * o->n + t]; }
static inline long om_hub(const Omega *o, int t, int bar, int k) { return o->base + 10L * t + 5 * bar + k; }
/* the 2*alpha copy neighbours of hub (t,bar,k) */
static void om_hub_nbrs(const Omega *o, int t, int bar, int k, long *out) {
    int j = 0;
    for (int B = 0; B < o->A; B++) {
        int a = o->types[B] == 'a', c1, c2, in;
        if (a) { if (!bar) { c1 = k + 4; c2 = k + 1; in = 1; } else { c1 = k + 2; c2 = k + 3; in = 0; } }
        else   { if (!bar) { c1 = k + 3; c2 = k + 4; in = 0; } else { c1 = k + 4; c2 = k + 1; in = 1; } }
        c1 = 5 * B + c1 % 5; c2 = 5 * B + c2 % 5;
        out[j++] = in ? om_inner(o, c1, t) : om_outer(o, c1, t);
        out[j++] = in ? om_inner(o, c2, t) : om_outer(o, c2, t);
    }
}
static void om_build(Omega *o) {
    memset(o->deg, 0, sizeof(int) * o->NV);
    int n2 = 2 * o->n;
    for (int c = 0; c < o->C; c++) for (int v = 0; v < n2; v++) {
        long g = (long)c * n2 + v;
        for (int j = 0; j < o->deg1; j++) o->adj[g * o->maxd + o->deg[g]++] = c * n2 + o->badj[(long)v * o->deg1 + j];
    }
    long nb[64];
    for (int t = 0; t < o->n; t++) for (int bar = 0; bar < 2; bar++) for (int k = 0; k < 5; k++) {
        long h = om_hub(o, t, bar, k); om_hub_nbrs(o, t, bar, k, nb);
        for (int j = 0; j < 2 * o->A; j++) { o->adj[h * o->maxd + o->deg[h]++] = nb[j]; o->adj[nb[j] * o->maxd + o->deg[nb[j]]++] = h; }
    }
}
/* labelling file: text, C*n point indices for P (copy-major) then C*n line indices (0..n-1) for L */
static int om_read_lab(Omega *o, const char *path) {
    FILE *f = fopen(path, "r"); if (!f) { perror(path); return -1; }
    for (long i = 0; i < (long)o->C * o->n; i++) if (fscanf(f, "%d", &o->P[i]) != 1) return -1;
    for (long i = 0; i < (long)o->C * o->n; i++) if (fscanf(f, "%d", &o->L[i]) != 1) return -1;
    fclose(f);
    char *seen = malloc(o->n);
    for (int c = 0; c < o->C; c++) for (int w = 0; w < 2; w++) {
        int *X = w ? o->L : o->P; memset(seen, 0, o->n);
        for (int t = 0; t < o->n; t++) { int x = X[(long)c * o->n + t]; if (x < 0 || x >= o->n || seen[x]) { fprintf(stderr, "copy %d: not a bijection\n", c); return -1; } seen[x] = 1; }
    }
    free(seen); return 0;
}
static void om_write_lab(const Omega *o, const char *path) {
    FILE *f = fopen(path, "w");
    for (long i = 0; i < (long)o->C * o->n; i++) fprintf(f, "%d%c", o->P[i], (i + 1) % o->n ? ' ' : '\n');
    for (long i = 0; i < (long)o->C * o->n; i++) fprintf(f, "%d%c", o->L[i], (i + 1) % o->n ? ' ' : '\n');
    fclose(f);
}
static void om_write_edges(const Omega *o, const char *path) {
    FILE *f = fopen(path, "w"); fprintf(f, "%ld\n", o->NV);
    for (long v = 0; v < o->NV; v++) for (int j = 0; j < o->deg[v]; j++) if (o->adj[v * o->maxd + j] > v) fprintf(f, "%ld %d\n", v, o->adj[v * o->maxd + j]);
    fclose(f);
}
/* c1 (focused moves): om_far also keeps a uniform reservoir sample of up to SMP_CAP far (source, target) pairs of
   the evaluation (only when smp_on).  smp_rs is a private RNG so the annealing stream is unchanged. */
#define SMP_CAP 64
static long smp_src[SMP_CAP], smp_tgt[SMP_CAP]; static int smp_n = 0, smp_on = 0; static long smp_seen = 0;
static uint64_t smp_rs = 0x853C49E6748FEA9BULL;
static inline uint64_t smp_rnd(void) { smp_rs ^= smp_rs << 13; smp_rs ^= smp_rs >> 7; smp_rs ^= smp_rs << 17; return smp_rs; }
static inline void smp_add(long s, long x) {
    smp_seen++;
    if (smp_n < SMP_CAP) { smp_src[smp_n] = s; smp_tgt[smp_n] = x; smp_n++; }
    else { uint64_t j = smp_rnd() % (uint64_t)smp_seen; if (j < SMP_CAP) { smp_src[j] = s; smp_tgt[j] = x; } }
}
/* bit-parallel BFS from sources src[0..ns): number of (source, vertex) pairs at distance > D; ecc/witness */
static long om_far(const Omega *o, const long *src, int ns, int D, int *maxecc, long *wu, long *wv) {
    long NV = o->NV, bad = 0; uint64_t *vis = malloc(8 * NV), *fr = malloc(8 * NV), *nx = malloc(8 * NV);
    if (maxecc) *maxecc = 0;
    smp_seen = 0; smp_n = 0;
    for (int s0 = 0; s0 < ns; s0 += 64) {
        int k = ns - s0 < 64 ? ns - s0 : 64; uint64_t full = k == 64 ? ~0ULL : ((1ULL << k) - 1);
        memset(vis, 0, 8 * NV); memset(fr, 0, 8 * NV);
        for (int i = 0; i < k; i++) { vis[src[s0 + i]] |= 1ULL << i; fr[src[s0 + i]] |= 1ULL << i; }
        int lev = 0;
        for (;;) {
            int any = 0;
            for (long x = 0; x < NV; x++) { uint64_t acc = 0; const int *a = o->adj + x * o->maxd; for (int j = 0; j < o->deg[x]; j++) acc |= fr[a[j]]; nx[x] = acc & ~vis[x]; any |= nx[x] != 0; }
            if (!any) break;
            lev++; for (long x = 0; x < NV; x++) vis[x] |= nx[x];
            uint64_t *tt = fr; fr = nx; nx = tt;
            if (lev == D) {   /* count pairs beyond D */
                for (long x = 0; x < NV; x++) { uint64_t m = ~vis[x] & full; if (m) { bad += __builtin_popcountll(m); if (wu && *wu < 0) { *wu = src[s0 + __builtin_ctzll(m)]; *wv = x; }
                    if (smp_on) for (uint64_t mm = m; mm; mm &= mm - 1) smp_add(src[s0 + __builtin_ctzll(mm)], x); } }
                if (!maxecc) break;
            }
            if (maxecc && lev > *maxecc) *maxecc = lev;
        }
        if (maxecc) for (long x = 0; x < NV; x++) if ((~vis[x] & full)) { *maxecc = 1 << 20; }
    }
    free(vis); free(fr); free(nx); return bad;
}
