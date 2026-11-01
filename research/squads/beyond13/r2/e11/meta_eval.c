/* e11: holes of Haar graphs H(G,S), G = Z_m x|_r Z_k (metacyclic), random symmetric S (e in S).
 * Usage: meta_holes m k r D nsamples seed
 * For each sample prints: |S|, coverage of the side-A ball of radius D-1 (fraction of G), holes on A and B
 * (elements at distance > D-1 from (e,A) resp. (e,B)), the cross check (ecc within D), and holes split by j=0 / j!=0.
 * Element (a,j) = index a*k+j. Product (a1,j1)(a2,j2) = (a1 + r^j1 a2, j1+j2). Graph: (g,A)~(s g,B), s in S. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

static long m, k, r, G;
static long *rp;             /* r^j mod m */
static long mul_a(long a1, long j1, long a2) { return (a1 + (long)((int64_t)rp[j1] * a2 % m)) % m; }

static uint64_t rs;
static uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }

/* BFS on the Haar graph from (src,side). dist array of size 2G, -1 = unseen. returns eccentricity */
static int *dist, *queue;
static int inv_idx[64], sidx[64], dS;
static int bfs(long src, int side) {
    for (long i = 0; i < 2 * G; i++) dist[i] = -1;
    long h = 0, t = 0;
    long start = 2 * src + side;
    dist[start] = 0; queue[t++] = (int)start;
    int ecc = 0;
    while (h < t) {
        long v = queue[h++];
        long g = v >> 1; int sd = v & 1;
        long a = g / k, j = g % k;
        int dv = dist[v];
        if (dv > ecc) ecc = dv;
        for (int q = 0; q < dS; q++) {
            long na, nj, ng;
            if (sd == 0) { /* (g,A) -> (s g, B), s = sidx[q] */
                long sa = sidx[q] / k, sj = sidx[q] % k;
                na = mul_a(sa, sj, a); nj = (sj + j) % k;
            } else {       /* (g,B) -> (s^-1 g, A) */
                long sa = inv_idx[q] / k, sj = inv_idx[q] % k;
                na = mul_a(sa, sj, a); nj = (sj + j) % k;
            }
            ng = na * k + nj;
            long w = 2 * ng + (1 - sd);
            if (dist[w] < 0) { dist[w] = dv + 1; queue[t++] = (int)w; }
        }
    }
    if (t < 2 * G) return 1000000; /* disconnected */
    return ecc;
}

int main(int argc, char **argv) {
    if (argc < 7) { fprintf(stderr, "usage: m k r D nsamples seed\n"); return 1; }
    m = atol(argv[1]); k = atol(argv[2]); r = atol(argv[3]);
    int D = atoi(argv[4]); int ns = atoi(argv[5]); rs = strtoull(argv[6], 0, 10) * 2654435761ULL + 88172645463325252ULL;
    G = m * k;
    rp = malloc(sizeof(long) * k);
    rp[0] = 1 % m;
    for (long j = 1; j < k; j++) rp[j] = (rp[j - 1] * r) % m;
    if (rp[k - 1] * r % m != 1 % m) { fprintf(stderr, "r^k != 1 mod m\n"); return 1; }
    dist = malloc(sizeof(int) * 2 * G); queue = malloc(sizeof(int) * 2 * G);
    int Delta = 4;
    if (getenv("DELTA")) Delta = atoi(getenv("DELTA"));
    dS = Delta;
    long sumcov = 0; double sumh = 0; long mincost = 1L << 60;
    int nvalid = 0;
    int fixed = getenv("FIXS") != NULL;
    if (fixed) { ns = 1; }
    for (int it = 0; it < ns; it++) {
        if (fixed) {
            char *p = getenv("FIXS"); int q = 0;
            while (*p && q < Delta) { long fa, fj, nn; if (sscanf(p, "%ld,%ld%ln", &fa, &fj, &nn) != 2) break; sidx[q++] = (int)(fa * k + fj); p += nn; while (*p == ' ') p++; }
            if (q != Delta) { fprintf(stderr, "FIXS needs %d entries\n", Delta); return 1; }
        } else {
        /* S = {e} + Delta-1 random distinct non-identity elements */
        sidx[0] = 0;
        for (int q = 1; q < Delta; q++) {
            long x; int ok;
            do { x = (long)(rnd() % G); ok = (x != 0); for (int p = 1; p < q && ok; p++) if (sidx[p] == x) ok = 0; } while (!ok);
            sidx[q] = (int)x;
        }
        }
        /* inverses */
        for (int q = 0; q < Delta; q++) {
            long sa = sidx[q] / k, sj = sidx[q] % k;
            /* s^-1 = (a', -j) with s^-1 = (-r^{-j} a, -j) */
            long jm = (k - sj) % k;
            long rinv = 1; /* r^{-j} = r^{(k-j)%k} */
            long a_inv = (m - (long)((int64_t)rp[jm] * sa % m)) % m;
            (void)rinv;
            inv_idx[q] = (int)(a_inv * k + jm);
        }
        /* check S^-1 is the right set: s * s^-1 = e */
        int okinv = 1;
        for (int q = 0; q < Delta; q++) {
            long sa = sidx[q] / k, sj = sidx[q] % k, ia = inv_idx[q] / k, ij = inv_idx[q] % k;
            long pa = mul_a(sa, sj, ia), pj = (sj + ij) % k;
            if (pa != 0 || pj != 0) okinv = 0;
        }
        if (!okinv) { fprintf(stderr, "inverse error\n"); return 1; }
        int eccA = bfs(0, 0);
        /* holes: elements at distance > D-1 on same side from (e,A): compute from BFS */
        long holesA = 0, holesAj0 = 0, holesB = 0, holesBj0 = 0, cntA = 0;
        for (long g = 0; g < G; g++) {
            int d = dist[2 * g];
            if (d < 0 || d > D - 1) { holesA++; if (g % k == 0) holesAj0++; }
            else cntA++;
        }
        long eccB_holes = 0;
        int eccB = bfs(0, 1);
        for (long g = 0; g < G; g++) {
            int d = dist[2 * g + 1];
            if (d < 0 || d > D - 1) { holesB++; if (g % k == 0) holesBj0++; }
        }
        (void)eccB_holes;
        if (fixed && getenv("LIST")) {
            int cnt = 0;
            for (long g = 0; g < G && cnt < 400; g++) { int d = dist[2*g]; if (d < 0 || d > D-1) { printf("HOLE A a=%ld j=%ld\n", g/k, g%k); cnt++; } }
            for (long g = 0; g < G && cnt < 800; g++) { int d = dist[2*g+1]; if (d < 0 || d > D-1) { printf("HOLE B a=%ld j=%ld\n", g/k, g%k); cnt++; } }
        }
        int ok = (eccA <= D && eccB <= D);
        double cost = (double)(holesA + holesB);
        if (ok) nvalid++;
        printf("sample %d S=[", it);
        for (int q = 0; q < Delta; q++) printf("%s(%ld,%ld)", q ? " " : "", sidx[q] / k, sidx[q] % k);
        printf("] ecc_A=%d ecc_B=%d holesA=%ld (j0 %ld) holesB=%ld (j0 %ld) cover=%.6f cost=%.0f %s\n",
               eccA, eccB, holesA, holesAj0, holesB, holesBj0, (double)cntA / G, cost, ok ? "DIAM_OK" : "");
        sumcov += cntA; sumh += cost; if ((long)cost < mincost) mincost = (long)cost;
    }
    printf("SUMMARY m=%ld k=%ld r=%ld N_side=%ld D=%d Delta=%d samples=%d valid=%d mean_cost=%.2f min_cost=%ld mean_cover=%.6f\n",
           m, k, r, G, D, Delta, ns, nvalid, sumh / ns, mincost, (double)sumcov / ((double)ns * G));
    return 0;
}
