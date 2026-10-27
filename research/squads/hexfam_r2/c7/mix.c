/* mix.c: iterated local search over pairs (r, s) = (point, line) of H(q) satisfying the Lemma 3 condition
   of THEOREM.md (hexagon-family): all pairwise distances in {4,6} with d(r,r') = d(s,s'), R pairwise
   non-collinear, S pairwise non-concurrent, and the midpoint -> midline map well defined and injective.
   Pairwise compatibility is kept in a conflict table conf[x][y] = number of state pairs incompatible with (x,y);
   the midpoint/midline consistency is checked exactly (valid_state) before every accepted move.
   usage: mix HEXBIN SECONDS SEED MODE(mixed|pure) INIT(-|file of "r s" lines) OUTPREFIX
   Writes OUTPREFIX_best_K.txt ("r s" per line) whenever the best size improves. */
#include "../../../projects/hexagon-family/tools/q6.h"
#include <time.h>
#define MAXK 400
#define MAXC 4000000
static Hex h; static int N, L, Q1, V, pure;
static uint8_t *DP, *DL, *conf; static int16_t *MP, *ML;
static int *que, *par; static uint8_t *dist;
static int K, Rs[MAXK], Ss[MAXK], bestK, bestR[MAXK], bestS[MAXK];
static uint8_t *inR, *inS;
static long *tabP, *tabL;
static int *zst, *wst, *zmapW, *wmapZ; static int stampc = 0;
static uint64_t rs = 88172645463325252ULL;
static inline uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static double now(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return t.tv_sec + 1e-9 * t.tv_nsec; }
static inline int compat(int a, int b) { if (a != b || a < 4) return 0; if (pure && a == 4) return 0; return 1; }
static void bfs(int src) {   /* nodes: points 0..N-1, lines N..N+L-1 */
    memset(dist, 255, V); int hd = 0, tl = 0; que[tl++] = src; dist[src] = 0; par[src] = -1;
    while (hd < tl) { int v = que[hd++]; if (dist[v] >= 6) continue;
        if (v < N) { for (int k = 0; k < Q1; k++) { int w = N + h.PL[(size_t)v * Q1 + k]; if (dist[w] == 255) { dist[w] = dist[v] + 1; par[w] = v; que[tl++] = w; } } }
        else { int l = v - N; for (int k = 0; k < Q1; k++) { int w = h.LP[(size_t)l * Q1 + k]; if (dist[w] == 255) { dist[w] = dist[v] + 1; par[w] = v; que[tl++] = w; } } }
    }
}
static void build_tables(void) {
    for (int s = 0; s < N; s++) { bfs(s);
        for (int t = 0; t < N; t++) { DP[(size_t)s * N + t] = dist[t]; MP[(size_t)s * N + t] = (dist[t] == 4) ? (int16_t)par[par[t]] : -1; } }
    for (int s = 0; s < L; s++) { bfs(N + s);
        for (int t = 0; t < L; t++) { DL[(size_t)s * L + t] = dist[N + t]; ML[(size_t)s * L + t] = (dist[N + t] == 4) ? (int16_t)(par[par[N + t]] - N) : -1; } }
}
/* exact Lemma 3 check of the first k state pairs (pairwise distances + midpoint/midline bijection) */
static int valid_state(int k) {
    stampc++;
    for (int i = 0; i < k; i++) for (int j = i + 1; j < k; j++) {
        int a = DP[(size_t)Rs[i] * N + Rs[j]], b = DL[(size_t)Ss[i] * L + Ss[j]];
        if (!compat(a, b)) return 0;
        if (a == 4) { int z = MP[(size_t)Rs[i] * N + Rs[j]], w = ML[(size_t)Ss[i] * L + Ss[j]];
            if (zst[z] == stampc && zmapW[z] != w) return 0;
            if (wst[w] == stampc && wmapZ[w] != z) return 0;
            zst[z] = wst[w] = stampc; zmapW[z] = w; wmapZ[w] = z; }
    }
    return 1;
}
static uint8_t INC[4][4];   /* INC[a/2][b/2] = 1 iff a point pair at distance a and line pair at distance b are incompatible */
static void apply(int r, int s, int sign) {   /* add (sign +1) or remove (-1) the state pair (r,s) from conf */
    const uint8_t *rowP = DP + (size_t)r * N, *rowL = DL + (size_t)s * L;
    uint8_t *tmp = malloc(L * 4);
    for (int a = 0; a < 4; a++) for (int y = 0; y < L; y++) tmp[a * L + y] = INC[a][rowL[y] >> 1];
    for (int x = 0; x < N; x++) { const uint8_t *ti = tmp + (size_t)(rowP[x] >> 1) * L; uint8_t *c = conf + (size_t)x * L;
        if (sign > 0) for (int y = 0; y < L; y++) c[y] += ti[y]; else for (int y = 0; y < L; y++) c[y] -= ti[y]; }
    free(tmp);
}
static void rebuild_conf(void) {
    memset(conf, 0, (size_t)N * L);
    for (int i = 0; i < K; i++) apply(Rs[i], Ss[i], +1);
}
static void save_best(const char *pre) {
    char fn[512]; snprintf(fn, sizeof fn, "%s_best_%d.txt", pre, bestK); FILE *f = fopen(fn, "w");
    for (int i = 0; i < bestK; i++) fprintf(f, "%d %d\n", bestR[i], bestS[i]); fclose(f);
}
int main(int argc, char **argv) {
    if (argc < 7) { fprintf(stderr, "usage: mix HEXBIN SECONDS SEED mixed|pure INIT|- OUTPREFIX\n"); return 1; }
    h = hex_load(argv[1]); double secs = atof(argv[2]); rs ^= (uint64_t)atoll(argv[3]) * 0x9E3779B97F4A7C15ULL; for (int i = 0; i < 20; i++) rnd();
    pure = !strcmp(argv[4], "pure"); const char *initf = argv[5], *pre = argv[6];
    N = h.N; L = h.L; Q1 = h.q + 1; V = N + L;
    for (int a = 0; a < 4; a++) for (int b = 0; b < 4; b++) INC[a][b] = !compat(2 * a, 2 * b);
    DP = malloc((size_t)N * N); DL = malloc((size_t)L * L); MP = malloc(2 * (size_t)N * N); ML = malloc(2 * (size_t)L * L);
    conf = malloc((size_t)N * L); que = malloc(sizeof(int) * V); par = malloc(sizeof(int) * V); dist = malloc(V);
    inR = calloc(N, 1); inS = calloc(L, 1); tabP = calloc(N, sizeof(long)); tabL = calloc(L, sizeof(long));
    zst = calloc(N, sizeof(int)); zmapW = malloc(sizeof(int) * N); wst = calloc(L, sizeof(int)); wmapZ = malloc(sizeof(int) * L);
    double t0 = now(); build_tables(); fprintf(stderr, "tables built in %.1fs (q=%d N=%d L=%d pure=%d)\n", now() - t0, h.q, N, L, pure);
    K = 0;
    if (strcmp(initf, "-")) { FILE *f = fopen(initf, "r"); int r, s; while (K < MAXK && fscanf(f, "%d %d", &r, &s) == 2) { Rs[K] = r; Ss[K] = s; K++; } fclose(f); }
    if (!valid_state(K)) { fprintf(stderr, "initial state invalid\n"); return 1; }
    for (int i = 0; i < K; i++) { inR[Rs[i]] = 1; inS[Ss[i]] = 1; }
    rebuild_conf();
    bestK = K; memcpy(bestR, Rs, sizeof(int) * K); memcpy(bestS, Ss, sizeof(int) * K);
    int *C0 = malloc(sizeof(int) * MAXC), *C1 = malloc(sizeof(int) * MAXC);
    long it = 0, lastImp = 0; int PERT = 400; double ts = now();
    while (now() - t0 < secs) {
        it++;
        int nc0 = 0, nc1 = 0;
        for (int x = 0; x < N; x++) { if (inR[x]) continue; const uint8_t *cr = conf + (size_t)x * L;
            for (int y = 0; y < L; y++) { if (inS[y]) continue; int v = cr[y];
                if (v == 0) { if (nc0 < MAXC) C0[nc0++] = x * L + y; } else if (v == 1) { if (nc1 < MAXC) C1[nc1++] = x * L + y; } } }
        int moves = 0;
        for (int att = 0; att < 300 && (nc0 || nc1); att++) {
            if (nc0 && (nc1 == 0 || rnd() % 3 == 0)) {
                int c = C0[rnd() % nc0], x = c / L, y = c % L;
                if (conf[c] != 0 || inR[x] || inS[y] || tabP[x] > it || tabL[y] > it || K >= MAXK) continue;
                Rs[K] = x; Ss[K] = y; K++;
                if (valid_state(K)) { apply(x, y, +1); inR[x] = 1; inS[y] = 1; moves++; } else K--;
            } else if (nc1) {
                int c = C1[rnd() % nc1], x = c / L, y = c % L;
                if (conf[c] != 1 || inR[x] || inS[y] || tabP[x] > it || tabL[y] > it) continue;
                int j = -1; for (int i = 0; i < K; i++) if (!compat(DP[(size_t)x * N + Rs[i]], DL[(size_t)y * L + Ss[i]])) { j = i; break; }
                if (j < 0) continue;
                int rj = Rs[j], sj = Ss[j]; Rs[j] = x; Ss[j] = y;
                if (valid_state(K)) { apply(rj, sj, -1); apply(x, y, +1); inR[rj] = 0; inS[sj] = 0; inR[x] = 1; inS[y] = 1;
                    tabP[rj] = it + 7 + rnd() % 10; tabL[sj] = it + 7 + rnd() % 10; moves++; }
                else { Rs[j] = rj; Ss[j] = sj; }
            }
        }
        if (K > bestK) { bestK = K; memcpy(bestR, Rs, sizeof(int) * K); memcpy(bestS, Ss, sizeof(int) * K); save_best(pre); lastImp = it;
            fprintf(stderr, "it %ld t=%.0fs NEW BEST %d (valid)\n", it, now() - t0, bestK); }
        if (it - lastImp > PERT) {   /* restore best and kick */
            K = bestK; memcpy(Rs, bestR, sizeof(int) * K); memcpy(Ss, bestS, sizeof(int) * K);
            memset(inR, 0, N); memset(inS, 0, L); for (int i = 0; i < K; i++) { inR[Rs[i]] = 1; inS[Ss[i]] = 1; }
            rebuild_conf();
            int kick = 2 + rnd() % 3;
            for (int k = 0; k < kick && K > 0; k++) { int i = rnd() % K; apply(Rs[i], Ss[i], -1); inR[Rs[i]] = 0; inS[Ss[i]] = 0;
                tabP[Rs[i]] = it + 15; tabL[Ss[i]] = it + 15; Rs[i] = Rs[K - 1]; Ss[i] = Ss[K - 1]; K--; }
            lastImp = it;
        }
        if (it % 50 == 0) fprintf(stderr, "it %ld t=%.0fs K=%d best=%d nc0=%d nc1=%d moves=%d\n", it, now() - t0, K, bestK, nc0, nc1, moves);
    }
    if (!valid_state(bestK)) { /* bestR/bestS copies */ }
    memcpy(Rs, bestR, sizeof(int) * bestK); memcpy(Ss, bestS, sizeof(int) * bestK);
    printf("BEST %d valid=%d iterations=%ld\n", bestK, valid_state(bestK), it);
    return 0;
}
