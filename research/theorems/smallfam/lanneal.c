/* lanneal.c: simulated annealing for regular voltage lifts of a small bipartite base over any group given by a
   multiplication table (hx.c 'tab' format).  Base file as for lx.c ("k", then edges "w b" or "w b = e").
   Lift: (w, g) ~ (b, a_e g).  Cost = sum over base vertices u of #lift vertices farther than D from (u, e)
   (right multiplication is an automorphism, so this is the exact diameter test).
   Move: change one free voltage to the best of K candidates; a candidate is random or (prob TARGP) targeted: take an
   uncovered pair (u, (v, h)), walk randomly a steps from (u, e) and b steps back from (v, h) (a + b + 1 <= D) and, if
   a free edge joins the two end base vertices, set its voltage so that it joins the two walk ends.
   Parallel edges keep distinct voltages.
   Usage: lanneal TABLE BASE D SECONDS SEED K OUT       (writes OUT "SOL v1 v2 ..." (free voltages) at cost 0)
   Env: TMAX (2), COOL (20), REHEAT (60), TARGP (0.5).
*/
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/time.h>

static int N, E, *T, *INV, D, K, NE, NF, EW[64], EB[64], FIX[64], FREE[64], DEG[16], ADJE[16][16], COLOR[16];
static uint64_t rs = 88172645463325252ULL;
static inline uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static double now(void) { struct timeval tv; gettimeofday(&tv, NULL); return tv.tv_sec + 1e-6 * tv.tv_usec; }
static inline int mul(int x, int y) { return T[(size_t)x * N + y]; }
static int *dist, *q, *uncu, *uncv, nunc;

static int cost(const int *V, int collect) {
    int n = K * N, total = 0; nunc = 0;
    for (int u = 0; u < K; u++) {
        for (int i = 0; i < n; i++) dist[i] = -1;
        int head = 0, tail = 0; dist[u * N + E] = 0; q[tail++] = u * N + E; int reached = 1;
        while (head < tail) {
            int v = q[head++], x = v / N, g = v % N, d = dist[v];
            if (d >= D) continue;
            for (int t = 0; t < DEG[x]; t++) {
                int e = ADJE[x][t], y, h;
                if (COLOR[x] == 0) { y = EB[e]; h = mul(V[e], g); } else { y = EW[e]; h = mul(INV[V[e]], g); }
                int w = y * N + h;
                if (dist[w] < 0) { dist[w] = d + 1; q[tail++] = w; reached++; }
            }
        }
        total += n - reached;
        if (collect) for (int i = 0; i < n && nunc < 4 * N; i++) if (dist[i] < 0) { uncu[nunc] = u; uncv[nunc] = i; nunc++; }
    }
    return total;
}

static void walk(const int *V, int x, int g, int len, int *ox, int *og) {
    int last = -1;
    for (int t = 0; t < len; t++) {
        int c, e; do { c = rnd() % DEG[x]; e = ADJE[x][c]; } while (e == last && DEG[x] > 1);
        if (COLOR[x] == 0) { g = mul(V[e], g); x = EB[e]; } else { g = mul(INV[V[e]], g); x = EW[e]; }
        last = e;
    }
    *ox = x; *og = g;
}

static int parallel_ok(const int *V) {
    for (int e = 0; e < NE; e++) for (int f = e + 1; f < NE; f++) if (EW[e] == EW[f] && EB[e] == EB[f] && V[e] == V[f]) return 0;
    return 1;
}

int main(int argc, char **argv) {
    if (argc < 8) { fprintf(stderr, "usage: lanneal TABLE BASE D SECONDS SEED K OUT\n"); return 2; }
    FILE *f = fopen(argv[1], "r"); if (!f) { perror("table"); return 2; }
    if (fscanf(f, "%d %d", &N, &E) != 2) return 2;
    T = malloc(sizeof(int) * (size_t)N * N);
    for (size_t i = 0; i < (size_t)N * N; i++) if (fscanf(f, "%d", &T[i]) != 1) return 2;
    fclose(f);
    FILE *bf = fopen(argv[2], "r"); if (!bf) { perror("base"); return 2; }
    char line[256]; K = -1; NE = 0;
    while (fgets(line, sizeof line, bf)) {
        if (line[0] == '#' || line[0] == '\n') continue;
        if (K < 0) { K = atoi(line); continue; }
        int w, b; char eq[8] = ""; int got = sscanf(line, "%d %d %7s", &w, &b, eq);
        if (got < 2) continue;
        EW[NE] = w; EB[NE] = b; FIX[NE] = (got == 3 && eq[0] == '='); NE++;
    }
    fclose(bf);
    for (int u = 0; u < K; u++) DEG[u] = 0;
    for (int e = 0; e < NE; e++) { COLOR[EW[e]] = 0; COLOR[EB[e]] = 1; ADJE[EW[e]][DEG[EW[e]]++] = e; ADJE[EB[e]][DEG[EB[e]]++] = e; }
    NF = 0; for (int e = 0; e < NE; e++) if (!FIX[e]) FREE[NF++] = e;
    D = atoi(argv[3]); double secs = atof(argv[4]); rs ^= (uint64_t)atoll(argv[5]) * 0x9E3779B97F4A7C15ULL;
    int KC = atoi(argv[6]); const char *out = argv[7];
    double TMAX = getenv("TMAX") ? atof(getenv("TMAX")) : 2.0, COOL = getenv("COOL") ? atof(getenv("COOL")) : 20;
    double REHEAT = getenv("REHEAT") ? atof(getenv("REHEAT")) : 60, TARGP = getenv("TARGP") ? atof(getenv("TARGP")) : 0.5;
    INV = malloc(sizeof(int) * N);
    for (int x = 0; x < N; x++) for (int y = 0; y < N; y++) if (mul(x, y) == E) { INV[x] = y; break; }
    dist = malloc(sizeof(int) * K * N); q = malloc(sizeof(int) * K * N); uncu = malloc(sizeof(int) * 4 * N); uncv = malloc(sizeof(int) * 4 * N);
    int V[64], best[64], cand[64];
    for (int e = 0; e < NE; e++) V[e] = E;
    do { for (int t = 0; t < NF; t++) V[FREE[t]] = rnd() % N; } while (!parallel_ok(V));
    int c = cost(V, 1), bc = c; memcpy(best, V, sizeof V);
    int *su = malloc(sizeof(int) * 4 * N), *sv = malloc(sizeof(int) * 4 * N), ns = nunc;
    memcpy(su, uncu, sizeof(int) * nunc); memcpy(sv, uncv, sizeof(int) * nunc);
    double t0 = now(), tstart = t0, tlast = t0, lastgain = t0, Tcur = TMAX; long long evals = 1;
    while (bc > 0 && now() - tstart < secs) {
        int bestc = 1 << 30, bt = -1, bx = -1;
        for (int kk = 0; kk < KC; kk++) {
            int t = rnd() % NF, x = rnd() % N;
            if (ns > 0 && (rnd() % 1000) < TARGP * 1000) {
                int pick = rnd() % ns, u = su[pick], tv = sv[pick], tx = tv / N, tg = tv % N;
                int a = rnd() % D, b = D - 1 - a; if (b < 0) b = 0;
                int x1, g1, x2, g2; walk(V, u, E, a, &x1, &g1); walk(V, tx, tg, b, &x2, &g2);
                /* free edge between x1 and x2? */
                int found = -1;
                for (int s = 0; s < NF; s++) { int e = FREE[s];
                    if ((EW[e] == x1 && EB[e] == x2) || (EW[e] == x2 && EB[e] == x1)) { found = s; if (rnd() & 1) break; } }
                if (found >= 0) {
                    t = found; int e = FREE[t];
                    if (EW[e] == x1) x = mul(g2, INV[g1]); else x = mul(g1, INV[g2]);
                }
            }
            memcpy(cand, V, sizeof V); cand[FREE[t]] = x;
            if (!parallel_ok(cand)) continue;
            int cc = cost(cand, 0); evals++;
            if (cc < bestc) { bestc = cc; bt = t; bx = x; }
        }
        if (bt < 0) continue;
        double dlt = bestc - c;
        if (dlt <= 0 || (double)(rnd() % 1000000) / 1e6 < exp(-dlt / Tcur)) {
            V[FREE[bt]] = bx; c = cost(V, 1); ns = nunc; memcpy(su, uncu, sizeof(int) * nunc); memcpy(sv, uncv, sizeof(int) * nunc);
            if (c < bc) { bc = c; memcpy(best, V, sizeof V); lastgain = now(); }
        }
        double tn = now();
        Tcur = TMAX * pow(0.5, (tn - t0) / COOL); if (Tcur < 0.05) Tcur = 0.05;
        if (tn - lastgain > REHEAT) { memcpy(V, best, sizeof V); c = cost(V, 1); ns = nunc; memcpy(su, uncu, sizeof(int) * nunc); memcpy(sv, uncv, sizeof(int) * nunc); lastgain = tn; t0 = tn; }
        if (tn - tlast > 30) { fprintf(stderr, "t=%.0f evals=%lld cost=%d best=%d\n", tn - tstart, evals, c, bc); tlast = tn; }
    }
    printf("RESULT N=%d K=%d D=%d best=%d evals=%lld voltages", N, K, D, bc, evals);
    for (int t = 0; t < NF; t++) printf(" %d", best[FREE[t]]);
    printf("\n");
    if (bc == 0) { FILE *o = fopen(out, "w"); fprintf(o, "SOL"); for (int t = 0; t < NF; t++) fprintf(o, " %d", best[FREE[t]]); fprintf(o, "\n"); fclose(o); }
    return 0;
}
