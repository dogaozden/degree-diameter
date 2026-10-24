/* pcover: anneal the matchings of a "polygon cover" (structured voltage lift).
 *
 * Base: incidence graph of a generalized polygon (points 0..P-1, lines P..2P-1) plus j perfect matchings
 * sigma_t : points -> lines.  Lift by Z_M: polygon edges carry voltage 0 (or a fixed voltage file, see VOLT),
 * matching t carries voltage T[t].  Lifted vertex (x, c) = x*M + c.
 *   point (p,c) ~ (L,c) for p on L;   point (p,c) ~ (sigma_t(p), c + T[t]).
 * Z_M acts by translation, so the diameter is max over base vertices s of ecc((s,0)).
 * Cost = sum over base vertices s of #{lifted vertices at distance > D from (s,0)}.
 * Moves: swap sigma_t(p1) <-> sigma_t(p2) (keeps sigma_t a bijection).  Metropolis on the cost.
 *
 * usage: pcover BASEFILE D M seed iters T1 T2 ... Tj      (env: TEMP0=, TEMP1=, OUT=solution file)
 * The base file is the output of polygons.py.  Prints the best cost; writes the matchings on success.
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <stdint.h>

static int P, Q1, j, M, D, V, NV;   /* Q1 = points per line = lines per point */
static int *lines;    /* P x Q1 : points on line */
static int *thru;     /* P x Q1 : lines through point */
static int *T;        /* j voltages */
static int *sig, *sinv;  /* j x P : sigma_t(p) (line index 0..P-1), inverse */
static int8_t *dist;
static int *queue;

static uint64_t rs;
static inline uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }

static long bfs_cost(int s) {   /* s: base vertex 0..2P-1 ; returns #lifted vertices at distance > D */
    memset(dist, -1, NV);
    int qh = 0, qt = 0;
    int v0 = s * M;
    dist[v0] = 0; queue[qt++] = v0;
    long reached = 1;
    while (qh < qt) {
        int u = queue[qh++];
        int du = dist[u];
        if (du == D) continue;
        int x = u / M, c = u % M;
        if (x < P) {           /* point x, copy c */
            for (int k = 0; k < Q1; k++) {
                int w = (P + thru[x * Q1 + k]) * M + c;
                if (dist[w] < 0) { dist[w] = du + 1; queue[qt++] = w; reached++; }
            }
            for (int t = 0; t < j; t++) {
                int cc = c + T[t]; if (cc >= M) cc -= M;
                int w = (P + sig[t * P + x]) * M + cc;
                if (dist[w] < 0) { dist[w] = du + 1; queue[qt++] = w; reached++; }
            }
        } else {               /* line x-P */
            int l = x - P;
            for (int k = 0; k < Q1; k++) {
                int w = lines[l * Q1 + k] * M + c;
                if (dist[w] < 0) { dist[w] = du + 1; queue[qt++] = w; reached++; }
            }
            for (int t = 0; t < j; t++) {
                int cc = c - T[t]; if (cc < 0) cc += M;
                int w = sinv[t * P + l] * M + cc;
                if (dist[w] < 0) { dist[w] = du + 1; queue[qt++] = w; reached++; }
            }
        }
    }
    return NV - reached;
}

static long total_cost(long cap) {
    long c = 0;
    for (int s = 0; s < 2 * P; s++) { c += bfs_cost(s); if (c > cap) return c; }
    return c;
}

int main(int argc, char **argv) {
    if (argc < 7) { fprintf(stderr, "usage: pcover BASE D M seed iters T1..Tj\n"); return 1; }
    FILE *f = fopen(argv[1], "r");
    D = atoi(argv[2]); M = atoi(argv[3]); rs = 88172645463325252ULL ^ (uint64_t)atoll(argv[4]) * 2654435761ULL;
    long iters = atol(argv[5]);
    j = argc - 6;
    T = malloc(sizeof(int) * j);
    for (int t = 0; t < j; t++) T[t] = ((atoi(argv[6 + t]) % M) + M) % M;
    if (fscanf(f, "%d", &P) != 1) return 1;
    /* read lines: count points per line from the first line */
    char buf[1 << 16];
    fgets(buf, sizeof buf, f);
    int *tmp = malloc(sizeof(int) * P * 64);
    int nl = 0; Q1 = 0;
    while (fgets(buf, sizeof buf, f)) {
        int k = 0; char *p = buf, *e;
        while (1) { long v = strtol(p, &e, 10); if (p == e) break; tmp[nl * 64 + k++] = (int)v; p = e; }
        if (k == 0) continue;
        if (!Q1) Q1 = k;
        nl++;
    }
    lines = malloc(sizeof(int) * P * Q1); thru = malloc(sizeof(int) * P * Q1);
    int *cnt = calloc(P, sizeof(int));
    for (int l = 0; l < P; l++) for (int k = 0; k < Q1; k++) {
        int p = tmp[l * 64 + k]; lines[l * Q1 + k] = p; thru[p * Q1 + cnt[p]++] = l;
    }
    V = 2 * P; NV = V * M;
    dist = malloc(NV); queue = malloc(sizeof(int) * NV);
    sig = malloc(sizeof(int) * j * P); sinv = malloc(sizeof(int) * j * P);
    for (int t = 0; t < j; t++) {
        for (int p = 0; p < P; p++) sig[t * P + p] = p;
        for (int p = P - 1; p > 0; p--) { int r = rnd() % (p + 1); int x = sig[t * P + p]; sig[t * P + p] = sig[t * P + r]; sig[t * P + r] = x; }
        for (int p = 0; p < P; p++) sinv[t * P + sig[t * P + p]] = p;
    }
    double T0 = getenv("TEMP0") ? atof(getenv("TEMP0")) : 2.0;
    double T1 = getenv("TEMP1") ? atof(getenv("TEMP1")) : 0.05;
    long cur = total_cost(1L << 60), best = cur;
    int *bsig = malloc(sizeof(int) * j * P); memcpy(bsig, sig, sizeof(int) * j * P);
    fprintf(stderr, "P=%d Q1=%d j=%d M=%d D=%d vertices=%d initial cost %ld\n", P, Q1, j, M, D, NV, cur);
    for (long it = 0; it < iters && best > 0; it++) {
        double temp = T0 * pow(T1 / T0, (double)it / iters);
        int t = rnd() % j, p1 = rnd() % P, p2 = rnd() % P;
        if (p1 == p2) continue;
        int l1 = sig[t * P + p1], l2 = sig[t * P + p2];
        sig[t * P + p1] = l2; sig[t * P + p2] = l1; sinv[t * P + l2] = p1; sinv[t * P + l1] = p2;
        /* accept threshold: new cost must be < cur - temp*ln(u) */
        double u = (rnd() >> 11) * (1.0 / 9007199254740992.0);
        long cap = cur + (long)(-temp * log(u + 1e-300)) ;
        long nc = total_cost(cap);
        if (nc <= cap) {
            cur = nc;
            if (cur < best) { best = cur; memcpy(bsig, sig, sizeof(int) * j * P);
                fprintf(stderr, "it %ld temp %.3f best %ld\n", it, temp, best); }
        } else {
            sig[t * P + p1] = l1; sig[t * P + p2] = l2; sinv[t * P + l1] = p1; sinv[t * P + l2] = p2;
        }
    }
    printf("RESULT best %ld M %d D %d j %d vertices %d\n", best, M, D, j, NV);
    char *out = getenv("OUT");
    if (out) {
        FILE *g = fopen(out, "w");
        fprintf(g, "# pcover base %s D %d M %d T", argv[1], D, M);
        for (int t = 0; t < j; t++) fprintf(g, " %d", T[t]);
        fprintf(g, " best %ld\n", best);
        for (int t = 0; t < j; t++) { for (int p = 0; p < P; p++) fprintf(g, "%d ", bsig[t * P + p]); fprintf(g, "\n"); }
        fclose(g);
    }
    return 0;
}
