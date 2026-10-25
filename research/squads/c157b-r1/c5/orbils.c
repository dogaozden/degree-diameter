/* orbils (ILS, ARW-style (1,1)/(1,2)-swaps, weighted, journal undo): weighted independent set on the orbit graph of lines of H(11) (c5 card).
 * Orbit o (a set of lines) is usable iff no point lies on two of its lines. Two usable orbits conflict iff some point
 * lies on a line of each. Weight = orbit size. Simulated annealing over insertions (insert v, drop its chosen
 * neighbours), with restarts from the best set.
 * usage: orbmis HEXBIN LABELS SECONDS SEED OUT [TFAC0 TFAC1 ITERS]
 * LABELS: int32 per line (orbit id). OUT: line ids, one per line (union of chosen orbits). */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

static double now(void) { struct timespec ts; clock_gettime(CLOCK_MONOTONIC, &ts); return ts.tv_sec + 1e-9 * ts.tv_nsec; }
static uint64_t rs = 88172645463325252ULL;
static inline uint64_t xr(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static inline double ur(void) { return (xr() >> 11) * (1.0 / 9007199254740992.0); }

int main(int argc, char **argv) {
    if (argc < 6) { fprintf(stderr, "usage: orbmis HEXBIN LABELS SECONDS SEED OUT [TFAC0 TFAC1 ITERS]\n"); return 1; }
    double secs = atof(argv[3]);
    rs ^= (uint64_t)atoll(argv[4]) * 0x9E3779B97F4A7C15ULL; for (int i = 0; i < 10; i++) xr();
    double tf0 = argc > 6 ? atof(argv[6]) : 0.4, tf1 = argc > 7 ? atof(argv[7]) : 0.03;
    long iters = argc > 8 ? atol(argv[8]) : 2000000;
    /* hex */
    FILE *f = fopen(argv[1], "rb"); if (!f) { perror("hex"); return 1; }
    int32_t hdr[3]; if (fread(hdr, 4, 3, f) != 3) return 1;
    int q = hdr[0], N = hdr[1], L = hdr[2], Q1 = q + 1;
    int32_t *LP = malloc(sizeof(int32_t) * (size_t)L * Q1);
    if (fread(LP, 4, (size_t)L * Q1, f) != (size_t)L * Q1) return 1; fclose(f);
    int32_t *lab = malloc(sizeof(int32_t) * L);
    f = fopen(argv[2], "rb"); if (!f) { perror("labels"); return 1; }
    if (fread(lab, 4, L, f) != (size_t)L) { fprintf(stderr, "bad labels\n"); return 1; } fclose(f);
    int K = 0; for (int l = 0; l < L; l++) if (lab[l] + 1 > K) K = lab[l] + 1;
    int *osz = calloc(K, sizeof(int)); for (int l = 0; l < L; l++) osz[lab[l]]++;
    /* point -> lines through it (each point on Q1 lines) */
    int32_t *PL = malloc(sizeof(int32_t) * (size_t)N * Q1); int *pc = calloc(N, sizeof(int));
    for (int l = 0; l < L; l++) for (int j = 0; j < Q1; j++) { int p = LP[(size_t)l * Q1 + j]; if (pc[p] >= Q1) { fprintf(stderr, "point degree\n"); return 1; } PL[(size_t)p * Q1 + pc[p]++] = l; }
    /* validity: orbit invalid iff two of its lines share a point */
    char *invalid = calloc(K, 1);
    for (int p = 0; p < N; p++) for (int j = 0; j < Q1; j++) for (int k = 0; k < j; k++)
        if (lab[PL[(size_t)p * Q1 + j]] == lab[PL[(size_t)p * Q1 + k]]) invalid[lab[PL[(size_t)p * Q1 + j]]] = 1;
    int *vid = malloc(sizeof(int) * K); int V = 0; int *vorb = malloc(sizeof(int) * K);
    for (int o = 0; o < K; o++) { if (!invalid[o] && osz[o] > 0) { vid[o] = V; vorb[V] = o; V++; } else vid[o] = -1; }
    /* members of valid orbits */
    int *mstart = calloc(V + 1, sizeof(int)); for (int v = 0; v < V; v++) mstart[v + 1] = mstart[v] + osz[vorb[v]];
    int *mem = malloc(sizeof(int) * (size_t)L); int *mfill = calloc(V, sizeof(int));
    for (int l = 0; l < L; l++) { int o = lab[l]; if (vid[o] < 0) continue; int v = vid[o]; mem[mstart[v] + mfill[v]++] = l; }
    /* cover lists: valid orbits through each point (distinct, <= Q1) */
    int32_t *cov = malloc(sizeof(int32_t) * (size_t)N * Q1); int *cc = calloc(N, sizeof(int));
    for (int p = 0; p < N; p++) for (int j = 0; j < Q1; j++) { int o = lab[PL[(size_t)p * Q1 + j]]; if (vid[o] >= 0) cov[(size_t)p * Q1 + cc[p]++] = vid[o]; }
    /* adjacency (CSR), two passes */
    int *mark = calloc(V, sizeof(int)); int *deg = calloc(V, sizeof(int));
    for (int v = 0; v < V; v++) {
        int st = v + 1;
        for (int t = mstart[v]; t < mstart[v + 1]; t++) { int l = mem[t];
            for (int j = 0; j < Q1; j++) { int p = LP[(size_t)l * Q1 + j];
                for (int c = 0; c < cc[p]; c++) { int u = cov[(size_t)p * Q1 + c]; if (u != v && mark[u] != st) { mark[u] = st; deg[v]++; } } } }
    }
    long E2 = 0; int *ast = malloc(sizeof(int) * (V + 1)); ast[0] = 0;
    for (int v = 0; v < V; v++) { ast[v + 1] = ast[v] + deg[v]; E2 += deg[v]; }
    int *adj = malloc(sizeof(int) * (size_t)(E2 + 1));
    memset(mark, 0, sizeof(int) * V);
    for (int v = 0; v < V; v++) {
        int st = v + 1, k = ast[v];
        for (int t = mstart[v]; t < mstart[v + 1]; t++) { int l = mem[t];
            for (int j = 0; j < Q1; j++) { int p = LP[(size_t)l * Q1 + j];
                for (int c = 0; c < cc[p]; c++) { int u = cov[(size_t)p * Q1 + c]; if (u != v && mark[u] != st) { mark[u] = st; adj[k++] = u; } } } }
    }
    int *w = malloc(sizeof(int) * V); double wsum = 0; int wmax = 0, wmin = 1 << 30;
    for (int v = 0; v < V; v++) { w[v] = osz[vorb[v]]; wsum += w[v]; if (w[v] > wmax) wmax = w[v]; if (w[v] < wmin) wmin = w[v]; }
    double wbar = wsum / (V ? V : 1);
    fprintf(stderr, "orbits K=%d usable V=%d (lines covered %d) avg deg %.1f  wmin %d wmax %d\n", K, V, mstart[V], V ? (double)E2 / V : 0.0, wmin, wmax);
    /* ILS state */
    int W64 = (V + 63) / 64; uint64_t *bits = calloc((size_t)V * W64, sizeof(uint64_t));
    for (int v = 0; v < V; v++) for (int k = ast[v]; k < ast[v + 1]; k++) { int u = adj[k]; bits[(size_t)v * W64 + (u >> 6)] |= 1ULL << (u & 63); }
    #define ADJ(a, b) ((bits[(size_t)(a) * W64 + ((b) >> 6)] >> ((b) & 63)) & 1ULL)
    char *inS = calloc(V, 1); int *tight = calloc(V, sizeof(int)); long *sumw = calloc(V, sizeof(long));
    int *sl = malloc(sizeof(int) * V); int *spos = malloc(sizeof(int) * V); int nS = 0; long totalW = 0;
    size_t JCAP = (size_t)1 << 22; int *jl = malloc(sizeof(int) * JCAP); size_t jn = 0;
    char *bestS = calloc(V, 1); long bestW = -1, curW = 0; double tbest = 0;
    #define RAW_ADD(X) do { int _ra = (X); inS[_ra] = 1; spos[_ra] = nS; sl[nS++] = _ra; totalW += w[_ra]; \
        for (int _rk = ast[_ra]; _rk < ast[_ra + 1]; _rk++) { int _rx = adj[_rk]; tight[_rx]++; sumw[_rx] += w[_ra]; } } while (0)
    #define RAW_REM(X) do { int _rr = (X); inS[_rr] = 0; int _rp = spos[_rr]; sl[_rp] = sl[--nS]; spos[sl[_rp]] = _rp; totalW -= w[_rr]; \
        for (int _rk = ast[_rr]; _rk < ast[_rr + 1]; _rk++) { int _rx = adj[_rk]; tight[_rx]--; sumw[_rx] -= w[_rr]; } } while (0)
    #define LOG(x) do { if (jn < JCAP) jl[jn++] = (x); } while (0)
    /* journal entries: (v<<1)|1 = v was added, (v<<1)|0 = v was removed */
    #define ADD_LOG(X) do { int _al = (X); RAW_ADD(_al); LOG((_al << 1) | 1); } while (0)
    #define REM_LOG(X) do { int _ml = (X); RAW_REM(_ml); LOG((_ml << 1)); } while (0)
    #define INSERT_LOG(X) do { int _il = (X); for (int _ik = ast[_il]; _ik < ast[_il + 1]; _ik++) { int _iu = adj[_ik]; if (inS[_iu]) REM_LOG(_iu); } ADD_LOG(_il); } while (0)
    if (argc > 9) { /* optional warm start: line ids of an independent set (e.g. a previous best) */
        FILE *fw = fopen(argv[9], "r"); int l; long added = 0;
        if (fw) { while (fscanf(fw, "%d", &l) == 1) { int v = vid[lab[l]]; if (v >= 0 && !inS[v] && tight[v] == 0) { RAW_ADD(v); added++; } } fclose(fw); }
        bestW = totalW; memcpy(bestS, inS, V); fprintf(stderr, "warm start: %ld orbits, weight %ld\n", added, totalW);
    }
    double t0 = now(); double wbar_ = wbar; double T = tf0 * wbar_;
    int *snap = malloc(sizeof(int) * V); int *U = malloc(sizeof(int) * V);
    long it = 0, lastimp = 0; long ncommit_worse = 0;
    while (now() - t0 < secs) {
        /* perturbation: force-insert a random non-solution vertex */
        int v = (int)(xr() % (uint64_t)V);
        if (inS[v]) continue;
        jn = 0; long before = totalW;
        INSERT_LOG(v);
        /* local search to a local optimum */
        int improved = 1;
        while (improved) {
            improved = 0;
            for (int x = 0; x < V; x++) if (!inS[x] && tight[x] == 0) { INSERT_LOG(x); improved = 1; }
            int ns = nS; memcpy(snap, sl, sizeof(int) * ns);
            for (int i = 0; i < ns; i++) {
                int x = snap[i]; if (!inS[x]) continue;
                int nu = 0;
                for (int k = ast[x]; k < ast[x + 1]; k++) { int u = adj[k]; if (!inS[u] && tight[u] == 1) U[nu++] = u; }
                int done = 0;
                for (int a = 0; a < nu && !done; a++) if (w[U[a]] > w[x]) { REM_LOG(x); INSERT_LOG(U[a]); done = 1; }
                for (int a = 0; a < nu && !done; a++) for (int b = a + 1; b < nu && !done; b++)
                    if (!ADJ(U[a], U[b]) && (long)w[U[a]] + w[U[b]] > w[x]) { REM_LOG(x); INSERT_LOG(U[a]); if (!inS[U[b]] && tight[U[b]] == 0) INSERT_LOG(U[b]); done = 1; }
                if (done) improved = 1;
            }
        }
        it++;
        long newW = totalW;
        if (newW >= before || jn >= JCAP - 100000 || ur() < exp((double)(newW - before) / T)) {
            if (newW < before) ncommit_worse++;
            jn = 0;
        } else {
            /* undo journal */
            for (size_t j = jn; j-- > 0;) { int e = jl[j]; int u = e >> 1; if (e & 1) RAW_REM(u); else RAW_ADD(u); }
            jn = 0;
        }
        if (totalW > bestW) { bestW = totalW; memcpy(bestS, inS, V); tbest = now() - t0; lastimp = it; }
        if (it - lastimp > 200000 && totalW < bestW) { /* restart from best */
            while (nS) RAW_REM(sl[nS - 1]);
            for (int u = 0; u < V; u++) if (bestS[u]) RAW_ADD(u);
            lastimp = it; jn = 0;
        }
        if (it % 20000 == 0) fprintf(stderr, "it %ld t=%.1f cur=%ld best=%ld (at %.1fs)\n", it, now() - t0, totalW, bestW, tbest);
    }
    /* output best */
    FILE *o = fopen(argv[5], "w"); long cnt = 0;
    for (int l = 0; l < L; l++) { int vv = vid[lab[l]]; if (vv >= 0 && bestS[vv]) { fprintf(o, "%d\n", l); cnt++; } }
    fclose(o);
    printf("RESULT K=%d V=%d best_lines=%ld iters=%ld time_best=%.1f\n", K, V, cnt, it, tbest);
    return 0;
}
