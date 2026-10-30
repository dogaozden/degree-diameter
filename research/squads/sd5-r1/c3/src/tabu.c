/* c3: tabu search over plain (not self-dual) Haar sets S, |S| = K = 6, e in S (WLOG: S -> tS gives an isomorphic
 * Haar graph). H(G,S) has diameter <= 5 iff X X = G and Y Y = G, X = S^-1 S, Y = S S^-1 (S X X = G then follows).
 * cost = |G \ XX| + |G \ YY| (0 = valid). Full neighbourhood: every (position i >= 1, element t not in S).
 * Tabu: an element removed from S may not come back for TEN steps unless it gives a new best (aspiration).
 * Restart from a random S after STAG steps without improvement of the run's best.
 * usage: tabu TABLE SEED SECONDS [OUTEDGES] [STAG] [TMIN TMAX]
 * TABLE format: "n ninv" / n rows of products i*j / inverse row (identity = index 0). Writes OUTEDGES when cost 0.  */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <stdint.h>

#define K 6
static int n;
static uint16_t *T, *INV;
static uint64_t *mk, *dk, mkc = 1, dkc = 1;
static int Xd[K * K], Yd[K * K];
static uint64_t rs = 88172645463325252ULL;
static inline uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }

static int cover(const int *L, int m) {
    int c = 0;
    mkc++;
    for (int a = 0; a < m; a++) {
        const uint16_t *row = T + (size_t)L[a] * n;
        for (int b = 0; b < m; b++) {
            int h = row[L[b]];
            if (mk[h] != mkc) { mk[h] = mkc; c++; }
        }
    }
    return c;
}

/* cost = (n - |XX|) + (n - |YY|) */
static int cost(const int *S) {
    int m = 0;
    dkc++;
    for (int i = 0; i < K; i++) {
        const uint16_t *row = T + (size_t)INV[S[i]] * n;      /* inv(s_i) * s_j */
        for (int j = 0; j < K; j++) {
            int x = row[S[j]];
            if (dk[x] != dkc) { dk[x] = dkc; Xd[m++] = x; }
        }
    }
    int cX = cover(Xd, m);
    m = 0;
    dkc++;
    for (int i = 0; i < K; i++) {
        const uint16_t *row = T + (size_t)S[i] * n;           /* s_i * inv(s_j) */
        for (int j = 0; j < K; j++) {
            int y = row[INV[S[j]]];
            if (dk[y] != dkc) { dk[y] = dkc; Yd[m++] = y; }
        }
    }
    int cY = cover(Yd, m);
    return 2 * n - cX - cY;
}

static double now(void) { struct timespec ts; clock_gettime(CLOCK_MONOTONIC, &ts); return ts.tv_sec + 1e-9 * ts.tv_nsec; }

int main(int argc, char **argv) {
    if (argc < 4) { fprintf(stderr, "usage: tabu TABLE SEED SECONDS [OUTEDGES] [STAG] [TMIN TMAX]\n"); return 1; }
    FILE *f = fopen(argv[1], "r");
    if (!f) { perror("table"); return 1; }
    int ninv;
    if (fscanf(f, "%d %d", &n, &ninv) != 2) return 1;
    T = malloc(sizeof(uint16_t) * n * n);
    INV = malloc(sizeof(uint16_t) * n);
    for (int i = 0; i < n * n; i++) { int v; if (fscanf(f, "%d", &v) != 1) return 1; T[i] = (uint16_t)v; }
    for (int i = 0; i < n; i++) { int v; if (fscanf(f, "%d", &v) != 1) return 1; INV[i] = (uint16_t)v; }
    fclose(f);
    mk = calloc(n, sizeof(uint64_t));
    dk = calloc(n, sizeof(uint64_t));
    uint64_t seed = (uint64_t)strtoull(argv[2], NULL, 10);
    rs ^= seed * 0x9E3779B97F4A7C15ULL; for (int i = 0; i < 10; i++) rnd();
    double secs = atof(argv[3]);
    const char *outf = (argc > 4 && strcmp(argv[4], "-") != 0) ? argv[4] : NULL;
    long stag = argc > 5 ? atol(argv[5]) : 4000;
    int tmin = argc > 7 ? atoi(argv[6]) : 5, tmax = argc > 7 ? atoi(argv[7]) : 15;
    if (tmax < tmin) tmax = tmin;

    int *tabu_until = calloc(n, sizeof(int));
    char *inS = calloc(n, 1);
    int S[K], bestS[K];
    int bestEver = 1 << 30;
    long step = 0, restarts = 0;
    double t0 = now();
    int found = 0;
    long evals = 0;

    while (!found) {
        /* random start: S[0] = identity (index 0), others random distinct non-identity */
        memset(inS, 0, n);
        memset(tabu_until, 0, sizeof(int) * n);
        S[0] = 0; inS[0] = 1;
        for (int i = 1; i < K; i++) {
            int t;
            do { t = 1 + (int)(rnd() % (uint64_t)(n - 1)); } while (inS[t]);
            S[i] = t; inS[t] = 1;
        }
        int cur = cost(S); evals++;
        int runBest = cur; long lastImp = 0; long it = 0;
        restarts++;
        while (1) {
            it++; step++;
            if ((step & 255) == 0 && now() - t0 > secs) goto done;
            int bc = 1 << 30, bi = -1, bt = -1, ties = 0;
            for (int i = 1; i < K; i++) {
                int old = S[i];
                for (int t = 1; t < n; t++) {
                    if (inS[t]) continue;
                    S[i] = t;
                    int c = cost(S); evals++;
                    int tabu = tabu_until[t] > it;
                    if (tabu && c >= bestEver) continue;       /* aspiration: only if new overall best */
                    if (c < bc) { bc = c; bi = i; bt = t; ties = 1; }
                    else if (c == bc) { ties++; if (rnd() % (uint64_t)ties == 0) { bi = i; bt = t; } }
                }
                S[i] = old;
            }
            if (bi < 0) break;                                   /* all moves tabu: restart */
            int old = S[bi];
            inS[old] = 0; inS[bt] = 1; S[bi] = bt;
            tabu_until[old] = (int)it + tmin + (int)(rnd() % (uint64_t)(tmax - tmin + 1));
            cur = bc;
            if (cur < runBest) { runBest = cur; lastImp = it; }
            if (cur < bestEver) {
                bestEver = cur; memcpy(bestS, S, sizeof S);
                fprintf(stderr, "best %d at step %ld restart %ld t=%.1fs evals %ld\n", bestEver, step, restarts, now() - t0, evals);
            }
            if (cur == 0) { found = 1; break; }
            if ((step % 20000) == 0) fprintf(stderr, "step %ld restart %ld cur %d bestEver %d t=%.1fs evals %ld\n", step, restarts, cur, bestEver, now() - t0, evals);
            if (it - lastImp > stag) break;                      /* restart */
        }
    }
done:
    if (found) {
        printf("FOUND cost 0 n=%d step=%ld restarts=%ld time=%.2fs evals=%ld\n", n, step, restarts, now() - t0, evals);
        printf("S =");
        for (int i = 0; i < K; i++) printf(" %d", S[i]);
        printf("\n");
        if (outf) {
            FILE *g = fopen(outf, "w");
            fprintf(g, "%d\n", 2 * n);
            for (int x = 0; x < n; x++)
                for (int i = 0; i < K; i++) fprintf(g, "%d %d\n", x, n + T[(size_t)S[i] * n + x]);
            fclose(g);
            printf("EDGES %s\n", outf);
        }
    } else {
        printf("NOT FOUND n=%d best_cost=%d steps=%ld restarts=%ld time=%.1fs evals=%ld\n", n, bestEver, step, restarts, now() - t0, evals);
        printf("best S =");
        for (int i = 0; i < K; i++) printf(" %d", bestS[i]);
        printf("\n");
    }
    return 0;
}
