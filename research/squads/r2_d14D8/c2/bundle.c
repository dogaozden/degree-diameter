/* bundle.c (squad r2_d14D8, card c2): geodesic-bundle diversity of hexagon voltages h: flags -> Z_k.
   Hex file: int32 q, N, L, then LP[l*(q+1)+j] (points of line l), as written by hexgen / hexlib.
   Vertices: points 0..N-1, lines N..2N-1. Flag f = l*(q+1)+j joins point LP[f] and line l, voltage hv[f] in Z_k.
   Signed walk sums: point->line adds hv[f], line->point subtracts hv[f] (as in the lift (p,g)~(l,g+v)).
   For a source s and each element t at hexagon distance 6 (opposite), the q+1 geodesics carry sums; msk[t] is
   the set of achieved sums (bitmask over Z_k), pc(t) = popcount = number of DISTINCT bundle voltages.
   mode 0: objective = sum pc(t); mode 1: objective = -sum (Dmax - pc)^2, Dmax = min(q+1, k).
   Local search: simulated annealing over single-flag changes on a fixed random source sample.
   usage: bundle HEX q k mode iters nsrc seed hin|rand hout [nfinal]
   hout: L lines of q+1 integers (hv[l*(q+1)+j] on line l, position j), the layout of mk_h.py. */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>

static int q, k, N, L, Q1, V, F, mode, Dmax;
static int32_t *LP;
static int *PF, *hv, *dist, *qu;
static uint32_t *msk, *pcnt;
static uint32_t FULLK;
static int check = 0;
static long long nchk_bad = 0;

static uint64_t rs = 88172645463325252ULL;
static uint64_t rnd64(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }
static int rndint(int n) { return (int)(rnd64() % (uint64_t)n); }

static inline uint32_t rot(uint32_t x, int c) {
    if (c == 0) return x;
    return ((x << c) | (x >> (k - c))) & FULLK;
}

/* BFS (depth 6) from s; msk[t] = set of signed geodesic sums (DP over the shortest-path DAG) */
static void bfs_from(int s) {
    for (int v = 0; v < V; v++) dist[v] = -1;
    int head = 0, tail = 0;
    dist[s] = 0; msk[s] = 1; if (check) pcnt[s] = 1;
    qu[tail++] = s;
    while (head < tail) {
        int u = qu[head++];
        int du = dist[u];
        if (du == 6) continue;
        if (u < N) {                                  /* point -> lines through it: +hv */
            for (int i = 0; i < Q1; i++) {
                int f = PF[u * Q1 + i];
                int w = N + f / Q1;
                if (dist[w] < 0) { dist[w] = du + 1; msk[w] = 0; if (check) pcnt[w] = 0; qu[tail++] = w; }
                if (dist[w] == du + 1) { msk[w] |= rot(msk[u], hv[f]); if (check) pcnt[w] += pcnt[u]; }
            }
        } else {                                      /* line -> its points: -hv */
            int l = u - N;
            for (int j = 0; j < Q1; j++) {
                int f = l * Q1 + j;
                int w = LP[f];
                int c = (k - hv[f]) % k;
                if (dist[w] < 0) { dist[w] = du + 1; msk[w] = 0; if (check) pcnt[w] = 0; qu[tail++] = w; }
                if (dist[w] == du + 1) { msk[w] |= rot(msk[u], c); if (check) pcnt[w] += pcnt[u]; }
            }
        }
    }
}

static double stats(const int *srcs, int ns, double *avgpc, int *minpc, double *fullfrac, long long *ntg) {
    double obj = 0; long long sum = 0, n = 0, full = 0; int mn = 1 << 30;
    for (int si = 0; si < ns; si++) {
        bfs_from(srcs[si]);
        for (int t = 0; t < V; t++) if (dist[t] == 6) {
            int pc = __builtin_popcount(msk[t]);
            sum += pc; n++; if (pc < mn) mn = pc; if (pc == Dmax) full++;
            if (mode == 1) { int d = Dmax - pc; obj -= (double)(d * d); } else obj += pc;
            if (check && pcnt[t] != (uint32_t)Q1) nchk_bad++;
        }
    }
    if (avgpc) *avgpc = n ? (double)sum / (double)n : 0;
    if (minpc) *minpc = mn;
    if (fullfrac) *fullfrac = n ? (double)full / (double)n : 0;
    if (ntg) *ntg = n;
    return obj;
}

static void shuffle_sources(int *perm, uint64_t sd) {
    uint64_t save = rs; rs = 0x2545F4914F6CDD1DULL ^ (sd * 0x9E3779B97F4A7C15ULL); for (int i = 0; i < 5; i++) rnd64();
    for (int i = 0; i < V; i++) perm[i] = i;
    for (int i = V - 1; i > 0; i--) { int j = rndint(i + 1); int t = perm[i]; perm[i] = perm[j]; perm[j] = t; }
    rs = save;
}

int main(int argc, char **argv) {
    if (argc < 10) { fprintf(stderr, "usage: bundle HEX q k mode iters nsrc seed hin|rand hout [nfinal]\n"); return 2; }
    const char *hexf = argv[1]; q = atoi(argv[2]); k = atoi(argv[3]); mode = atoi(argv[4]);
    long iters = atol(argv[5]); int nsrc = atoi(argv[6]); uint64_t seed = strtoull(argv[7], 0, 10);
    const char *hin = argv[8], *hout = argv[9]; int nfinal = argc > 10 ? atoi(argv[10]) : 2000;
    Q1 = q + 1; Dmax = Q1 < k ? Q1 : k; FULLK = (1u << k) - 1;
    FILE *f = fopen(hexf, "rb"); if (!f) { perror("hex"); return 2; }
    int32_t hdr[3]; if (fread(hdr, 4, 3, f) != 3) return 2;
    if (hdr[0] != q) { fprintf(stderr, "q mismatch\n"); return 2; }
    N = hdr[1]; L = hdr[2]; V = N + L; F = L * Q1;
    LP = malloc(4 * (size_t)F); if (fread(LP, 4, (size_t)F, f) != (size_t)F) return 2; fclose(f);
    PF = malloc(4 * (size_t)N * Q1); int *cnt = calloc(N, sizeof(int));
    for (int l = 0; l < L; l++) for (int j = 0; j < Q1; j++) { int p = LP[l * Q1 + j]; PF[p * Q1 + cnt[p]++] = l * Q1 + j; }
    for (int p = 0; p < N; p++) if (cnt[p] != Q1) { fprintf(stderr, "bad degree\n"); return 2; }
    hv = malloc(4 * (size_t)F); dist = malloc(4 * (size_t)V); qu = malloc(4 * (size_t)V);
    msk = malloc(4 * (size_t)V); pcnt = malloc(4 * (size_t)V);
    rs ^= seed * 0x9E3779B97F4A7C15ULL + 0x632BE59BD9B4E019ULL; if (!rs) rs = 1; for (int i = 0; i < 10; i++) rnd64();
    if (!strcmp(hin, "rand")) { for (int i = 0; i < F; i++) hv[i] = rndint(k); }
    else {
        FILE *g = fopen(hin, "r"); if (!g) { perror("hin"); return 2; }
        for (int i = 0; i < F; i++) { if (fscanf(g, "%d", &hv[i]) != 1) { fprintf(stderr, "short h file\n"); return 2; } hv[i] = ((hv[i] % k) + k) % k; }
        fclose(g);
    }
    int *h0 = malloc(4 * (size_t)F); memcpy(h0, hv, 4 * (size_t)F);
    int *perm = malloc(4 * (size_t)V);
    shuffle_sources(perm, seed + 11);
    int ns = nsrc < V ? nsrc : V;
    check = 1; double avg0; int min0; double full0; long long ntg0;
    double init = stats(perm, ns, &avg0, &min0, &full0, &ntg0);
    printf("check: geodesic-count mismatches %lld (targets %lld)\n", nchk_bad, ntg0); check = 0;
    double cur = init, best = init; int *besth = malloc(4 * (size_t)F); memcpy(besth, hv, 4 * (size_t)F);
    long long acc = 0;
    double T0 = 2.0, T1 = 0.05;
    for (long it = 0; it < iters; it++) {
        double T = T0 * pow(T1 / T0, (double)it / (double)(iters > 1 ? iters - 1 : 1));
        int fl = rndint(F); int old = hv[fl];
        int nw = (old + 1 + rndint(k - 1)) % k;
        hv[fl] = nw;
        double sc = stats(perm, ns, NULL, NULL, NULL, NULL);
        double d = sc - cur;
        if (d >= 0 || rnd01() < exp(d / T)) { cur = sc; acc++; if (cur > best) { best = cur; memcpy(besth, hv, 4 * (size_t)F); } }
        else hv[fl] = old;
    }
    /* final report on a fresh, larger sample: initial (random) h versus the best h found */
    int nf = nfinal < V ? nfinal : V;
    shuffle_sources(perm, seed + 977);
    double a1, a2, f1, f2; int m1, m2; long long nt1, nt2;
    memcpy(hv, h0, 4 * (size_t)F); double s1 = stats(perm, nf, &a1, &m1, &f1, &nt1);
    memcpy(hv, besth, 4 * (size_t)F); double s2 = stats(perm, nf, &a2, &m2, &f2, &nt2);
    printf("q=%d k=%d mode=%d iters=%ld nsrc=%d accepted=%lld | search obj init %.1f best %.1f | Dmax %d\n",
           q, k, mode, iters, ns, acc, init, best, Dmax);
    printf("  final sample (%d sources, %lld opposite pairs): random h: avg pc %.3f min %d frac_full %.4f obj %.1f\n",
           nf, nt1, a1, m1, f1, s1);
    printf("  final sample (%d sources, %lld opposite pairs): best  h: avg pc %.3f min %d frac_full %.4f obj %.1f\n",
           nf, nt2, a2, m2, f2, s2);
    FILE *o = fopen(hout, "w"); if (!o) { perror("hout"); return 2; }
    for (int l = 0; l < L; l++) { for (int j = 0; j < Q1; j++) fprintf(o, "%d%c", besth[l * Q1 + j], j == Q1 - 1 ? '\n' : ' '); }
    fclose(o);
    return 0;
}
