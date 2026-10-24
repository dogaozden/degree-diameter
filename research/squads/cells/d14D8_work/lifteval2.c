/* lifteval2.c: cyclic voltage lifts of a general base graph (loops and same-side edges allowed), cell-14-8 job.

   Base: n vertices, each with a colour c(v) in {0,1}; undirected edges (u, v, x) with voltage x in Z_m (u = v allowed:
   a loop (v,k) ~ (v,k+x)). Lift vertices (v, k), k in Z_m; (u, k) ~ (v, k + x).
   Lift colouring: col(v, k) = c(v) + MIX * k (mod 2). The lift must be bipartite in this colouring: every edge has to
   change colour, i.e. c(u) + MIX*k != c(v) + MIX*(k + x), checked on input. MIX = 1 needs m even.
   Z_m translations are automorphisms. Even D: the lift has diameter <= D iff from every (s, 0) every lift vertex of the
   other colour is reached by a walk of length exactly D - 1 (then same-colour pairs are within D). With MIX = 0 only
   colour-0 sources are needed (reverse + translate); with MIX = 1 sources of both colours are needed (default: all).

   Input (text): "n m MIX" then n colours c(0..n-1) (whitespace separated), then "u v x" edge lines.
   Usage: lifteval2 FILE D [srcspec] [verbose]   srcspec: all | r:K:seed | s:start:step | i:v1,v2,...
   Output: COST total sources ... ; exit 0 iff cost 0.  m <= 1024 (multiword masks). */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>

typedef uint64_t u64;
static int n, m, MIX, W;
static int *off, *adj, *vol;
static unsigned char *col;
static u64 LASTMASK;
static u64 *EVEN, *ODD; /* masks of even / odd k */

static inline void orrot(u64 *restrict out, const u64 *restrict x, int v) {
    if (W == 1) { u64 y = x[0]; if (v) y = ((y << v) | (y >> (m - v))) & LASTMASK; out[0] |= y; return; }
    if (v == 0) { for (int i = 0; i < W; i++) out[i] |= x[i]; return; }
    int ws = v >> 6, bs = v & 63;
    for (int i = W - 1; i >= ws; i--) { int s = i - ws; u64 val = x[s] << bs; if (bs && s >= 1) val |= x[s - 1] >> (64 - bs); if (i == W - 1) val &= LASTMASK; out[i] |= val; }
    int r = m - v, wr = r >> 6, br = r & 63;
    for (int i = 0; i + wr < W; i++) { int s = i + wr; u64 val = x[s] >> br; if (br && s + 1 < W) val |= x[s + 1] << (64 - br); out[i] |= val; }
}

static u64 rs = 0x9E3779B97F4A7C15ULL;
static u64 rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }

int main(int argc, char **argv) {
    if (argc < 3) { fprintf(stderr, "usage: lifteval2 FILE D [srcspec] [verbose]\n"); return 2; }
    FILE *f = fopen(argv[1], "r"); if (!f) { perror("open"); return 2; }
    int D = atoi(argv[2]);
    const char *spec = argc > 3 ? argv[3] : "all";
    int verbose = argc > 4 ? atoi(argv[4]) : 0;
    if (D % 2) { fprintf(stderr, "even D only\n"); return 2; }
    if (fscanf(f, "%d %d %d", &n, &m, &MIX) != 3 || m < 1 || m > 1024) { fprintf(stderr, "bad header\n"); return 2; }
    if (MIX && m % 2) { fprintf(stderr, "MIX needs m even\n"); return 2; }
    W = (m + 63) / 64; LASTMASK = (m % 64 == 0) ? ~0ULL : ((1ULL << (m % 64)) - 1);
    col = malloc(n);
    for (int i = 0; i < n; i++) { int c; if (fscanf(f, "%d", &c) != 1) { fprintf(stderr, "bad colours\n"); return 2; } col[i] = c & 1; }
    int cap = 1 << 20, ne = 0; int *eu = malloc(sizeof(int) * cap), *ev = malloc(sizeof(int) * cap), *ex = malloc(sizeof(int) * cap);
    int u, v, x;
    while (fscanf(f, "%d %d %d", &u, &v, &x) == 3) {
        if (u < 0 || u >= n || v < 0 || v >= n) { fprintf(stderr, "bad edge\n"); return 2; }
        x = ((x % m) + m) % m;
        if (((col[u] + col[v] + MIX * x) & 1) == 0) { fprintf(stderr, "edge %d %d %d does not change colour\n", u, v, x); return 2; }
        if (ne == cap) { cap *= 2; eu = realloc(eu, sizeof(int) * cap); ev = realloc(ev, sizeof(int) * cap); ex = realloc(ex, sizeof(int) * cap); }
        eu[ne] = u; ev[ne] = v; ex[ne] = x; ne++;
    }
    fclose(f);
    /* arcs: each edge gives u->v with +x and v->u with -x (a loop gives two arcs v->v with +x, -x) */
    off = calloc(n + 1, sizeof(int));
    for (int e = 0; e < ne; e++) { off[ev[e] + 1]++; off[eu[e] + 1]++; }  /* arcs indexed by head */
    int maxdeg = 0;
    for (int i = 0; i < n; i++) { if (off[i + 1] > maxdeg) maxdeg = off[i + 1]; off[i + 1] += off[i]; }
    adj = malloc(sizeof(int) * 2 * ne); vol = malloc(sizeof(int) * 2 * ne);
    int *pos = malloc(sizeof(int) * n); memcpy(pos, off, sizeof(int) * n);
    /* store incoming arcs per head: tail and voltage (pull formulation) */
    for (int e = 0; e < ne; e++) {
        adj[pos[ev[e]]] = eu[e]; vol[pos[ev[e]]++] = ex[e];               /* u -> v, +x */
        adj[pos[eu[e]]] = ev[e]; vol[pos[eu[e]]++] = (m - ex[e]) % m;     /* v -> u, -x */
    }
    long multi = 0;
    for (int i = 0; i < n; i++) for (int k = off[i]; k < off[i + 1]; k++) for (int k2 = off[i]; k2 < k; k2++) if (adj[k] == adj[k2] && vol[k] == vol[k2]) multi++;
    fprintf(stderr, "base n %d m %d MIX %d edges %d maxdeg %d lift %lld vertices; repeated arcs %ld\n", n, m, MIX, ne, maxdeg, (long long)n * m, multi);
    EVEN = calloc(W, sizeof(u64)); ODD = calloc(W, sizeof(u64));
    for (int k = 0; k < m; k++) { if (k % 2) ODD[k >> 6] |= 1ULL << (k & 63); else EVEN[k >> 6] |= 1ULL << (k & 63); }
    int nsrc = 0; int *src = malloc(sizeof(int) * (n + 8));
    if (!strcmp(spec, "all")) { for (int i = 0; i < n; i++) if (MIX || col[i] == 0) src[nsrc++] = i; }
    else if (spec[0] == 'r') { int K = 0; unsigned long long seed = 1; sscanf(spec, "r:%d:%llu", &K, &seed);
        rs = 0x9E3779B97F4A7C15ULL + (seed + 1) * 0xD1B54A32D192ED03ULL; if (!rs) rs = 1; for (int i = 0; i < 20; i++) rnd();
        while (nsrc < K) { int c = (int)(rnd() % (u64)n); if (MIX || col[c] == 0) src[nsrc++] = c; } }
    else if (spec[0] == 's') { int st = 0, sp = 1; sscanf(spec, "s:%d:%d", &st, &sp); for (int i = st; i < n; i += sp) if (MIX || col[i] == 0) src[nsrc++] = i; }
    else if (spec[0] == 'i') { const char *p = spec + 2; while (*p) { src[nsrc++] = atoi(p); while (*p && *p != ',') p++; if (*p) p++; } }
    u64 *cur = malloc(sizeof(u64) * n * W), *nxt = malloc(sizeof(u64) * n * W);
    long long total = 0, worstc = -1; int worst = -1, bad = 0;
    for (int s = 0; s < nsrc; s++) {
        memset(cur, 0, sizeof(u64) * n * W); cur[(size_t)src[s] * W] = 1;
        for (int step = 0; step < D - 1; step++) {
            memset(nxt, 0, sizeof(u64) * n * W);
            for (int h = 0; h < n; h++) for (int k = off[h]; k < off[h + 1]; k++) {
                const u64 *xx = cur + (size_t)adj[k] * W; int nz = 0; for (int i = 0; i < W; i++) nz |= xx[i] != 0;
                if (nz) orrot(nxt + (size_t)h * W, xx, vol[k]);
            }
            u64 *t = cur; cur = nxt; nxt = t;
        }
        /* targets: colour != colour of source (col[src] + 0) */
        long long unc = 0; int sc = col[src[s]];
        for (int v2 = 0; v2 < n; v2++) {
            const u64 *xx = cur + (size_t)v2 * W;
            int c = 0, need;
            if (!MIX) { if (col[v2] == sc) continue; for (int i = 0; i < W; i++) c += __builtin_popcountll(xx[i]); need = m; }
            else { /* other colour: col[v2] + k != sc  ->  k parity = 1 + sc + col[v2] */
                const u64 *P = ((1 + sc + col[v2]) & 1) ? ODD : EVEN;
                for (int i = 0; i < W; i++) c += __builtin_popcountll(xx[i] & P[i]); need = m / 2; }
            unc += need - c;
        }
        if (verbose && unc) fprintf(stderr, "src %d uncovered %lld\n", src[s], unc);
        if (unc) bad++;
        total += unc; if (unc > worstc) { worstc = unc; worst = src[s]; }
    }
    printf("COST %lld sources %d bad %d worst_src %d worst %lld maxdeg %d lift_vertices %lld\n", total, nsrc, bad, worst, worstc, maxdeg, (long long)n * m);
    return total ? 1 : 0;
}
