/* hgcheck.c (D7_THEOREMS.md, Section 5): check a hub graph HG(K1, K2; d): bipartite with colour classes of sizes K1
   (vertices 0..K1-1) and K2 (vertices K1..K1+K2-1), maximum degree <= d, every two vertices of the same colour at
   distance <= 6.  Bit-parallel BFS (64 sources per word) from every vertex, OpenMP over batches.
   Modes:
     hgcheck sol FILE.sol d          the "hubgraph" block of a typed_build.py solution (lines "a b": B-hub a, A-hub b)
     hgcheck rand K1 K2 d SEED        a random bipartite graph, degrees as equal as possible (<= d), no repeated edges
     hgcheck haar K d SEED [TRIES]    Haar graph of Z_K: x ~ x+s (s in S, |S| = d); same-colour distance <= 6 iff
                                      3(S - S) = Z_K, checked directly; random S, then simple local search
   Output: one RESULT line.  Build: cc -O2 -fopenmp -o hgcheck hgcheck.c */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>

static long n, K1, K2, *st, *adj; static long far_s = -1, far_x = -1;
static uint64_t rng = 88172645463325252ULL;
static uint64_t xr(void) { rng ^= rng << 13; rng ^= rng >> 7; rng ^= rng << 17; return rng; }

static void build_csr(long m, long *U, long *W) {
    long *deg = calloc(n + 1, sizeof(long));
    for (long i = 0; i < m; i++) { deg[U[i]]++; deg[W[i]]++; }
    st = calloc(n + 1, sizeof(long));
    for (long i = 0; i < n; i++) st[i + 1] = st[i] + deg[i];
    adj = malloc(2 * m * sizeof(long)); long *pos = calloc(n, sizeof(long));
    for (long i = 0; i < m; i++) { adj[st[U[i]] + pos[U[i]]++] = W[i]; adj[st[W[i]] + pos[W[i]]++] = U[i]; }
    free(deg); free(pos);
}

/* returns the number of ordered same-colour pairs at distance > 6 (or unreachable) */
static long far_pairs(int *maxecc) {
    long bad = 0; int ecc = 0;
    long nb = (n + 63) / 64;
    #pragma omp parallel reduction(+:bad) reduction(max:ecc)
    {
        uint64_t *vis = malloc(n * 8), *fr = malloc(n * 8), *nx = malloc(n * 8);
        #pragma omp for schedule(dynamic, 4)
        for (long b = 0; b < nb; b++) {
            long s0 = b * 64; int ns = (n - s0 < 64) ? (int)(n - s0) : 64;
            memset(vis, 0, n * 8); memset(fr, 0, n * 8);
            for (int k = 0; k < ns; k++) { vis[s0 + k] |= 1ULL << k; fr[s0 + k] |= 1ULL << k; }
            for (int lev = 1; lev <= 6; lev++) {
                for (long x = 0; x < n; x++) { uint64_t acc = 0; for (long i = st[x]; i < st[x + 1]; i++) acc |= fr[adj[i]]; nx[x] = acc & ~vis[x]; }
                for (long x = 0; x < n; x++) vis[x] |= nx[x];
                uint64_t *t = fr; fr = nx; nx = t;
            }
            /* same colour: source s and target x both < K1 or both >= K1 */
            for (int k = 0; k < ns; k++) {
                long s = s0 + k; long lo = s < K1 ? 0 : K1, hi = s < K1 ? K1 : n;
                for (long x = lo; x < hi; x++) if (!((vis[x] >> k) & 1)) { bad++; if ((xr() & 15) == 0) { far_s = s; far_x = x; } }
            }
        }
        free(vis); free(fr); free(nx);
    }
    *maxecc = ecc;
    return bad;
}

static int report(const char *what, int d) {
    long maxd = 0, mind = n; for (long x = 0; x < n; x++) { long k = st[x + 1] - st[x]; if (k > maxd) maxd = k; if (k < mind) mind = k; }
    for (long x = 0; x < n; x++) for (long i = st[x]; i < st[x + 1]; i++) {
        long y = adj[i]; if ((x < K1) == (y < K1)) { printf("RESULT INVALID not bipartite\n"); return 1; }
        for (long j = i + 1; j < st[x + 1]; j++) if (adj[j] == y) { printf("RESULT INVALID repeated edge\n"); return 1; } }
    int e; long bad = far_pairs(&e);
    printf("%s K1=%ld K2=%ld degree min=%ld max=%ld far_same_colour_pairs=%ld\n", what, K1, K2, mind, maxd, bad);
    if (bad == 0 && maxd <= d) printf("RESULT VALID HG(%ld,%ld;%d)\n", K1, K2, d); else printf("RESULT INVALID\n");
    return 0;
}

int main(int argc, char **argv) {
    if (argc < 3) { fprintf(stderr, "usage: see source\n"); return 2; }
    if (!strcmp(argv[1], "sol")) {
        FILE *f = fopen(argv[2], "r"); int d = atoi(argv[3]); char line[1 << 16]; long m = 0, *U = NULL, *W = NULL; int in = 0; long E = 0;
        while (fgets(line, sizeof line, f)) {
            if (!strncmp(line, "hubs ", 5)) sscanf(line + 5, "%ld %ld", &K1, &K2);
            else if (!strncmp(line, "hubgraph ", 9)) { sscanf(line + 9, "%ld", &E); U = malloc(E * 8); W = malloc(E * 8); in = 1; }
            else if (in && m < E) { long a, b; if (sscanf(line, "%ld %ld", &a, &b) == 2) { U[m] = a; W[m] = K1 + b; m++; } }
        }
        n = K1 + K2; build_csr(m, U, W); return report(argv[2], d);
    }
    if (!strcmp(argv[1], "edges")) {      /* first line K1 K2, then "a b" with 0 <= a < K1, 0 <= b < K2 */
        FILE *f = fopen(argv[2], "r"); int d = atoi(argv[3]); long cap = 1 << 20, m = 0, a, b;
        long *U = malloc(cap * 8), *W = malloc(cap * 8);
        if (fscanf(f, "%ld %ld", &K1, &K2) != 2) return 2;
        while (fscanf(f, "%ld %ld", &a, &b) == 2) { if (m == cap) { cap *= 2; U = realloc(U, cap * 8); W = realloc(W, cap * 8); }
            if (a < 0 || a >= K1 || b < 0 || b >= K2) { printf("RESULT INVALID bad edge\n"); return 1; } U[m] = a; W[m] = K1 + b; m++; }
        n = K1 + K2; build_csr(m, U, W); return report(argv[2], d);
    }
    if (!strcmp(argv[1], "rand")) {
        K1 = atol(argv[2]); K2 = atol(argv[3]); int d = atoi(argv[4]); rng ^= (uint64_t)atol(argv[5]) * 0x9E3779B97F4A7C15ULL; n = K1 + K2;
        /* edges: E = d * min(K1, K2); stubs on the smaller side d each, on the larger side as equal as possible */
        long small = K1 < K2 ? K1 : K2, E = (long)d * small;
        long *SA = malloc(E * 8), *SB = malloc(E * 8);
        for (long i = 0; i < E; i++) { SA[i] = i % K1; SB[i] = K1 + i % K2; }
        /* random pairing of the stubs, then remove repeated edges by swaps with random edges (a hash set of the
           (a, b) pairs keeps the swaps valid) */
        for (long i = E - 1; i > 0; i--) { long j = xr() % (i + 1); long t = SB[i]; SB[i] = SB[j]; SB[j] = t; }
        long H = 1; while (H < 4 * E) H <<= 1;
        uint64_t *hs = calloc(H, 8); long *mult = calloc(H, sizeof(long));
        #define KEY(a, b) ((uint64_t)(a) * 4294967311ULL + (uint64_t)(b) + 1)
        #define SLOT(k) ({ uint64_t _k = (k); long _h = (long)((_k * 0x9E3779B97F4A7C15ULL) >> 20) & (H - 1); while (hs[_h] && hs[_h] != _k) _h = (_h + 1) & (H - 1); _h; })
        for (long e = 0; e < E; e++) { long h = SLOT(KEY(SA[e], SB[e])); hs[h] = KEY(SA[e], SB[e]); mult[h]++; }
        long fixes = 0;
        for (int pass = 0; pass < 100; pass++) {
            long dups = 0;
            for (long e = 0; e < E; e++) {
                long h = SLOT(KEY(SA[e], SB[e]));
                if (mult[h] < 2) continue;
                dups++;
                for (int tr = 0; tr < 1000; tr++) {
                    long f = xr() % E; if (SA[f] == SA[e] || SB[f] == SB[e]) continue;
                    long h1 = SLOT(KEY(SA[e], SB[f])), h2 = SLOT(KEY(SA[f], SB[e]));
                    if (mult[h1] || mult[h2]) continue;
                    long hf = SLOT(KEY(SA[f], SB[f]));
                    mult[h]--; mult[hf]--;
                    long t = SB[e]; SB[e] = SB[f]; SB[f] = t;
                    h1 = SLOT(KEY(SA[e], SB[e])); hs[h1] = KEY(SA[e], SB[e]); mult[h1]++;
                    h2 = SLOT(KEY(SA[f], SB[f])); hs[h2] = KEY(SA[f], SB[f]); mult[h2]++;
                    fixes++; break;
                }
            }
            if (!dups) break;
        }
        free(hs); free(mult);
        build_csr(E, SA, SB);
        if (argc > 6 && !strcmp(argv[6], "repair")) {
            int e0; far_s = far_x = -1; long cur = far_pairs(&e0); int rounds = 0;
            int maxr = argc > 7 ? atoi(argv[7]) : 400;
            while (cur > 0 && rounds < maxr) {
                rounds++;
                long s = far_s, x = far_x; if (s < 0) break;
                /* make s adjacent to a neighbour c of x by a 2-switch */
                long c = adj[st[x] + xr() % (st[x + 1] - st[x])];
                long e1 = -1, e2 = -1, cand[64]; int nc = 0;
                if (s < K1) {           /* A colour: edges (SA, SB) with SA = s, and (a, c) with a != x */
                    for (long e = 0; e < E && nc < 64; e++) if (SA[e] == s) cand[nc++] = e;
                    e1 = cand[xr() % nc]; nc = 0;
                    for (long e = 0; e < E && nc < 64; e++) if (SB[e] == c && SA[e] != x && SA[e] != s) cand[nc++] = e;
                    if (!nc) continue; e2 = cand[xr() % nc];
                    long t = SB[e1]; SB[e1] = SB[e2]; SB[e2] = t;
                } else {                /* B colour: edges with SB = s, and (c, b) with b != x */
                    for (long e = 0; e < E && nc < 64; e++) if (SB[e] == s) cand[nc++] = e;
                    e1 = cand[xr() % nc]; nc = 0;
                    for (long e = 0; e < E && nc < 64; e++) if (SA[e] == c && SB[e] != x && SB[e] != s) cand[nc++] = e;
                    if (!nc) continue; e2 = cand[xr() % nc];
                    long t = SA[e1]; SA[e1] = SA[e2]; SA[e2] = t;
                }
                free(st); free(adj); build_csr(E, SA, SB);
                int dup = 0;
                for (long v = 0; v < n && !dup; v++) for (long i = st[v]; i < st[v + 1] && !dup; i++) for (long j = i + 1; j < st[v + 1]; j++) if (adj[i] == adj[j]) { dup = 1; break; }
                long save_s = far_s, save_x = far_x;
                long nw = dup ? cur + 1 : far_pairs(&e0);
                if (nw < cur) { cur = nw; fprintf(stderr, "repair round %d: far pairs %ld\n", rounds, cur); }
                else {
                    if (s < K1) { long t = SB[e1]; SB[e1] = SB[e2]; SB[e2] = t; } else { long t = SA[e1]; SA[e1] = SA[e2]; SA[e2] = t; }
                    free(st); free(adj); build_csr(E, SA, SB); far_s = save_s; far_x = save_x;
                }
            }
            FILE *g = fopen("hg_repaired_edges.txt", "w");
            if (g) { fprintf(g, "%ld %ld\n", K1, K2); for (long i = 0; i < E; i++) fprintf(g, "%ld %ld\n", SA[i], SB[i] - K1); fclose(g); }
        }
        char what[64]; snprintf(what, sizeof what, "rand seed=%s", argv[5]); return report(what, d);
    }
    if (!strcmp(argv[1], "haar")) {
        long K = atol(argv[2]); int d = atoi(argv[3]); rng ^= (uint64_t)atol(argv[4]) * 0x9E3779B97F4A7C15ULL; int tries = argc > 5 ? atoi(argv[5]) : 20;
        long nw = (K + 63) / 64; uint64_t *A = malloc(nw * 8), *B = malloc(nw * 8);
        long *S = malloc(d * 8), *D = malloc((long)d * d * 8);
        for (int t = 0; t < tries; t++) {
            for (int i = 0; i < d; i++) { again: S[i] = xr() % K; for (int j = 0; j < i; j++) if (S[j] == S[i]) goto again; }
            long nd = 0; char *seen = calloc(K, 1);
            for (int i = 0; i < d; i++) for (int j = 0; j < d; j++) { long x = ((S[i] - S[j]) % K + K) % K; if (!seen[x]) { seen[x] = 1; D[nd++] = x; } }
            free(seen);
            /* A = D; B = A + D; A = B + D */
            memset(A, 0, nw * 8); for (long i = 0; i < nd; i++) A[D[i] >> 6] |= 1ULL << (D[i] & 63);
            for (int round = 0; round < 2; round++) {
                memset(B, 0, nw * 8);
                for (long x = 0; x < K; x++) if ((A[x >> 6] >> (x & 63)) & 1) for (long i = 0; i < nd; i++) { long y = x + D[i]; if (y >= K) y -= K; B[y >> 6] |= 1ULL << (y & 63); }
                uint64_t *tmp = A; A = B; B = tmp;
            }
            long cov = 0; for (long x = 0; x < K; x++) cov += (A[x >> 6] >> (x & 63)) & 1;
            printf("haar K=%ld d=%d try=%d |S-S|=%ld covered=%ld S=", K, d, t, nd, cov);
            for (int i = 0; i < d; i++) printf("%ld%c", S[i], i + 1 < d ? ',' : '\n');
            if (cov == K) { printf("RESULT VALID HG(%ld,%ld;%d) Haar Z_%ld\n", K, K, d, K); return 0; }
        }
        printf("RESULT NOT FOUND\n"); return 1;
    }
    return 2;
}
