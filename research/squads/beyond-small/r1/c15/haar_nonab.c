// c15: simulated annealing for bipartite Haar graphs H(G,S) over a NON-ABELIAN group G, |S| = 17.
// Vertices A_g = g, B_h = M + h. Edges A_g ~ B_{s*g} for s in S (right translations are automorphisms,
// so only BFS from A_1 and B_1 are needed).
// Cost = #pairs violating diameter 5: A-targets at dist > 4 and B-targets at dist > 5 from A_1,
//        plus B-targets at dist > 4 from B_1. Cost 0 means diameter <= 5 (verify with apsp).
// Groups: GT=0 : AGL(1,p) = {x -> a x + b}, M = p(p-1).   GT=1 : Heisenberg group mod p, M = p^3.
// usage: haar_nonab GT p seconds seed outprefix
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <time.h>

#define D 17
static int GT, P, M;
static double now(void){ struct timespec ts; clock_gettime(CLOCK_MONOTONIC,&ts); return ts.tv_sec+ts.tv_nsec*1e-9; }
static int *EA, *EB, *EC;     // decoded coordinates
static int S[D], Sinv[D];
static int *LS, *LSi;         // LS[k*M+g] = s_k * g ; LSi[k*M+h] = s_k^{-1} * h
static int *dist, *q, *inS;

static inline int enc(int a, int b, int c) {
    if (GT == 0) return (a - 1) * P + b;
    return (a * P + b) * P + c;
}
static int mul(int x, int y) {
    int a = EA[x], b = EB[x], c = EC[x], a2 = EA[y], b2 = EB[y], c2 = EC[y];
    if (GT == 0) return enc((a * a2) % P, (a * b2 + b) % P, 0);
    return enc((a + a2) % P, (b + b2) % P, (int)(((long)c + c2 + (long)a * b2) % P));
}
static int inv(int x) {
    int a = EA[x], b = EB[x], c = EC[x];
    if (GT == 0) {
        int ai = 1;  // a^{-1} mod p by search (p small enough)
        for (int t = 1; t < P; t++) if ((a * t) % P == 1) { ai = t; break; }
        return enc(ai, (P - (ai * b) % P) % P, 0);
    }
    int na = (P - a) % P, nb = (P - b) % P;
    int nc = ((P - c) + (long)a * b) % P;
    return enc(na, nb, nc);
}

static void build_tables_row(int k) {
    int s = S[k], si = Sinv[k];
    for (int g = 0; g < M; g++) {
        LS[k * M + g] = mul(s, g);
        LSi[k * M + g] = mul(si, g);
    }
}

static int bfs_cost(void) {
    int viol = 0;
    for (int src = 0; src < 2 * M; src += M) {    // src = 0 (A_1) then src = M (B_1)
        for (int i = 0; i < 2 * M; i++) dist[i] = -1;
        int h = 0, t = 0;
        q[t++] = src; dist[src] = 0;
        while (h < t) {
            int v = q[h++], dv = dist[v];
            if (dv >= 5) continue;
            if (v < M) {
                for (int k = 0; k < D; k++) {
                    int u = M + LS[k * M + v];
                    if (dist[u] < 0) { dist[u] = dv + 1; q[t++] = u; }
                }
            } else {
                int hh = v - M;
                for (int k = 0; k < D; k++) {
                    int u = LSi[k * M + hh];
                    if (dist[u] < 0) { dist[u] = dv + 1; q[t++] = u; }
                }
            }
        }
        if (src == 0) {
            for (int g = 1; g < M; g++) if (dist[g] < 0 || dist[g] > 4) viol++;
            for (int hh = 0; hh < M; hh++) if (dist[M + hh] < 0 || dist[M + hh] > 5) viol++;
        } else {
            for (int hh = 1; hh < M; hh++) if (dist[M + hh] < 0 || dist[M + hh] > 4) viol++;
        }
    }
    return viol;
}

static double urand(void) { return (rand() + 0.5) / ((double)RAND_MAX + 1.0); }

int main(int argc, char **argv) {
    if (argc < 6) { fprintf(stderr, "usage: %s GT p seconds seed outprefix\n", argv[0]); return 1; }
    GT = atoi(argv[1]); P = atoi(argv[2]);
    double secs = atof(argv[3]); int seed = atoi(argv[4]); const char *outp = argv[5];
    M = (GT == 0) ? P * (P - 1) : P * P * P;
    srand(seed);
    EA = malloc(sizeof(int) * M); EB = malloc(sizeof(int) * M); EC = malloc(sizeof(int) * M);
    for (int x = 0; x < M; x++) {
        if (GT == 0) { EA[x] = x / P + 1; EB[x] = x % P; EC[x] = 0; }
        else { EC[x] = x % P; int t = x / P; EB[x] = t % P; EA[x] = t / P; }
    }
    LS = malloc(sizeof(int) * D * M); LSi = malloc(sizeof(int) * D * M);
    dist = malloc(sizeof(int) * 2 * M); q = malloc(sizeof(int) * 2 * M);
    inS = calloc(M, sizeof(int));
    // random initial S (distinct, not identity)
    for (int k = 0; k < D; k++) {
        int s;
        do { s = rand() % M; } while (inS[s] || s == 0);
        inS[s] = 1; S[k] = s;
    }
    for (int k = 0; k < D; k++) { Sinv[k] = inv(S[k]); build_tables_row(k); }
    int cur = bfs_cost(), best = cur;
    int bestS[D]; memcpy(bestS, S, sizeof S);
    int *savedS = malloc(sizeof(int) * M), *savedSi = malloc(sizeof(int) * M);
    double T0 = (argc > 6) ? atof(argv[6]) : 2.0, T1 = (argc > 7) ? atof(argv[7]) : 0.05;
    double c0 = now();
    long it = 0, acc = 0;
    while (1) {
        if ((it & 63) == 0) {
            double el = (now() - c0);
            if (el > secs) break;
        }
        it++;
        double el = (now() - c0);
        double T = T0 * pow(T1 / T0, el / secs);
        int k = rand() % D;
        int t;
        do { t = rand() % M; } while (inS[t] || t == 0);
        int old = S[k], oldi = Sinv[k];
        memcpy(savedS, LS + k * M, sizeof(int) * M);
        memcpy(savedSi, LSi + k * M, sizeof(int) * M);
        inS[old] = 0; inS[t] = 1;
        S[k] = t; Sinv[k] = inv(t); build_tables_row(k);
        int nc = bfs_cost();
        int delta = nc - cur;
        if (delta <= 0 || urand() < exp(-delta / T)) {
            cur = nc; acc++;
            if (cur < best) { best = cur; memcpy(bestS, S, sizeof S); }
            if (cur == 0) break;
        } else {
            inS[t] = 0; inS[old] = 1;
            S[k] = old; Sinv[k] = oldi;
            memcpy(LS + k * M, savedS, sizeof(int) * M);
            memcpy(LSi + k * M, savedSi, sizeof(int) * M);
        }
    }
    double el = (now() - c0);
    printf("GT=%d p=%d M=%d n=%d iters=%ld acc=%ld time=%.1fs best_cost=%d\n", GT, P, M, 2 * M, it, acc, el, best);
    printf("bestS");
    for (int k = 0; k < D; k++) printf(" %d", bestS[k]);
    printf("\n");
    if (best == 0) {
        // write edge list: A_g = g, B_h = M + h, edge A_g ~ B_{s g}
        char fn[512]; snprintf(fn, sizeof fn, "%s_n%d.edges", outp, 2 * M);
        FILE *f = fopen(fn, "w");
        fprintf(f, "%d\n", 2 * M);
        for (int k = 0; k < D; k++) {
            for (int g = 0; g < M; g++) fprintf(f, "%d %d\n", g, M + mul(bestS[k], g));
        }
        fclose(f);
        printf("WROTE %s\n", fn);
    }
    return 0;
}
