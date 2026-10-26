/* Card c1: D(3,7)-type graph on F_7^3 + F_7^3 (686 vertices).
 * Points a=(a1,a2,a3), lines b=(b1,b2,b3).
 * Full graph G (7-regular): a ~ b iff b2 = f(a1,b1) - a2, b3 = g(a1,b1,a2,b2) - a3, for each b1 in F_7.
 * Candidate 6-regular-ish subgraph: each point a drops the edge with b1 = rem[a]
 * (so points have degree 6; lines have degree 7 - #points dropping them; need <= 6).
 * Cost = number of same-side ordered pairs at distance > 4 (0 = valid diameter <= 5).
 * Search: random (f,g) polynomials, then simulated annealing over rem[] with penalty
 * lambda * (#lines of degree 7).
 * usage: d3rem SEED TRIALS ITERS OUTPREFIX
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <time.h>

#define Q 7
#define NP 343
#define NV 686
#define MAXD 8

static int pw[Q][4];

typedef struct { int n; int e[6][4]; int c[6]; } Poly;

static inline int evalp(const Poly *P, const int *x) {
    int s = 0;
    for (int t = 0; t < P->n; t++) {
        int m = P->c[t];
        for (int k = 0; k < 4; k++) m = m * pw[x[k]][P->e[t][k]] % Q;
        s += m;
    }
    return s % Q;
}

static int adj[NV][MAXD], deg[NV];
static int stampv[NV], dl[NV], queue_[NV];
static int stampc = 0;

static void build(const Poly *F, const Poly *G, const int *rem) {
    for (int v = 0; v < NV; v++) deg[v] = 0;
    for (int p = 0; p < NP; p++) {
        int a1 = p / 49, a2 = (p / 7) % 7, a3 = p % 7;
        for (int b1 = 0; b1 < Q; b1++) {
            if (rem[p] == b1) continue;
            int x[4] = {a1, b1, 0, 0};
            int f = evalp(F, x);
            int b2 = ((f - a2) % Q + Q) % Q;
            x[2] = a2; x[3] = b2;
            int gv = evalp(G, x);
            int b3 = ((gv - a3) % Q + Q) % Q;
            int L = NP + b1 * 49 + b2 * 7 + b3;
            adj[p][deg[p]++] = L;
            adj[L][deg[L]++] = p;
        }
    }
}

/* same-side pairs at distance > 4, summed over all 686 sources */
static long cost_full(void) {
    long total = 0;
    for (int s = 0; s < NV; s++) {
        stampc++;
        int head = 0, tail = 0;
        queue_[tail++] = s; stampv[s] = stampc; dl[s] = 0;
        while (head < tail) {
            int u = queue_[head++];
            int du = dl[u];
            if (du == 4) continue;
            for (int k = 0; k < deg[u]; k++) {
                int w = adj[u][k];
                if (stampv[w] != stampc) {
                    stampv[w] = stampc; dl[w] = du + 1; queue_[tail++] = w;
                }
            }
        }
        int same = 0;
        int sside = (s < NP);
        for (int i = 0; i < tail; i++) if ((queue_[i] < NP) == sside) same++;
        total += NP - same;
    }
    return total;
}

static int penalty(void) {
    int pen = 0;
    for (int L = NP; L < NV; L++) if (deg[L] > 6) pen++;
    return pen;
}

static void write_edges(const char *path, const int *rem) {
    FILE *f = fopen(path, "w");
    if (!f) return;
    fprintf(f, "%d\n", NV);
    for (int p = 0; p < NV; p++)
        for (int k = 0; k < deg[p]; k++) {
            int w = adj[p][k];
            if (p < NP) fprintf(f, "%d %d\n", p, w);
        }
    fclose(f);
}

static void randpoly(Poly *P, int maxn, int maxexp, int maxdeg, int nvars) {
    P->n = 1 + rand() % maxn;
    for (int t = 0; t < P->n; t++) {
        int tries = 0;
        for (;;) {
            int tot = 0;
            for (int k = 0; k < 4; k++) {
                P->e[t][k] = (k < nvars) ? rand() % (maxexp + 1) : 0;
                tot += P->e[t][k];
            }
            if (tot <= maxdeg && tot > 0) break;
            if (++tries > 100) { P->e[t][0] = 1; break; }
        }
        P->c[t] = 1 + rand() % 6;
    }
}

static void printpoly(const char *name, const Poly *P) {
    printf("%s =", name);
    for (int t = 0; t < P->n; t++)
        printf(" %+d*a1^%d*b1^%d*a2^%d*b2^%d", P->c[t], P->e[t][0], P->e[t][1], P->e[t][2], P->e[t][3]);
    printf("\n");
}


static void setp(Poly *P, int n, int c[][5]) { /* rows: c, e0,e1,e2,e3 */
    P->n = n;
    for (int t = 0; t < n; t++) { P->c[t] = c[t][0]; for (int k = 0; k < 4; k++) P->e[t][k] = c[t][k+1]; }
}

int main(int argc, char **argv) {
    unsigned seed = argc > 1 ? (unsigned)atoi(argv[1]) : (unsigned)time(NULL);
    int trials = argc > 2 ? atoi(argv[2]) : 10;
    int iters = argc > 3 ? atoi(argv[3]) : 1000;
    const char *outp = argc > 4 ? argv[4] : "best";
    srand(seed);
    for (int x = 0; x < Q; x++) {
        pw[x][0] = 1;
        for (int e = 1; e < 4; e++) pw[x][e] = pw[x][e - 1] * x % Q;
    }
    double lam = getenv("LAM") ? atof(getenv("LAM")) : 30.0;
    long gbest = -1;
    int ncand = 0;
    static int CF[8][3][5], CG[8][3][5]; static int nF[8], nG[8];
    if (trials == 0) {
        /* fixed candidates: terms {coef, e_a1, e_b1, e_a2, e_b2} */
        int i = 0;
        /* 0: D(3,q): b2=a1b1-a2, b3=a2b1-a3 */
        nF[i]=1; CF[i][0][0]=1; CF[i][0][1]=1; CF[i][0][2]=1; nG[i]=1; CG[i][0][0]=1; CG[i][0][2]=1; CG[i][0][3]=1; i++;
        /* 1: b3=a1b2-a3 */
        nF[i]=1; CF[i][0][0]=1; CF[i][0][1]=1; CF[i][0][2]=1; nG[i]=1; CG[i][0][0]=1; CG[i][0][1]=1; CG[i][0][4]=1; i++;
        /* 2: b3 = a2b1 + a1b2 */
        nF[i]=1; CF[i][0][0]=1; CF[i][0][1]=1; CF[i][0][2]=1; nG[i]=2; CG[i][0][0]=1; CG[i][0][2]=1; CG[i][0][3]=1; CG[i][1][0]=1; CG[i][1][1]=1; CG[i][1][4]=1; i++;
        /* 3: b3 = a1^2 b2 */
        nF[i]=1; CF[i][0][0]=1; CF[i][0][1]=1; CF[i][0][2]=1; nG[i]=1; CG[i][0][0]=1; CG[i][0][1]=2; CG[i][0][4]=1; i++;
        /* 4: b2 = a1 b1 - a2, b3 = a2 b1^2 */
        nF[i]=1; CF[i][0][0]=1; CF[i][0][1]=1; CF[i][0][2]=1; nG[i]=1; CG[i][0][0]=1; CG[i][0][2]=2; CG[i][0][3]=1; i++;
        /* 5: b2 = a1^2 b1 - a2, b3 = a2 b1 - a3 */
        nF[i]=1; CF[i][0][0]=1; CF[i][0][1]=2; CF[i][0][2]=1; nG[i]=1; CG[i][0][0]=1; CG[i][0][2]=1; CG[i][0][3]=1; i++;
        /* 6: b2 = a1 b1 - a2, b3 = a1 b1^2 + a2 b1 */
        nF[i]=1; CF[i][0][0]=1; CF[i][0][1]=1; CF[i][0][2]=1; nG[i]=2; CG[i][0][0]=1; CG[i][0][1]=1; CG[i][0][2]=2; CG[i][1][0]=1; CG[i][1][2]=1; CG[i][1][3]=1; i++;
        /* 7: b2 = a1 b1 - a2, b3 = a2 b1 + a1 b1^2 */
        nF[i]=1; CF[i][0][0]=1; CF[i][0][1]=1; CF[i][0][2]=1; nG[i]=2; CG[i][0][0]=1; CG[i][0][2]=1; CG[i][0][3]=1; CG[i][1][0]=1; CG[i][1][1]=1; CG[i][1][2]=2; i++;
        ncand = i;
    }
    if (iters < 0) {
        /* screen mode: random (F,G) with base 7-regular graph, no removal; report lowest base cost */
        long best = -1;
        for (int tr = 0; tr < trials; tr++) {
            Poly F, G;
            randpoly(&F, 3, 3, 3, 2);
            randpoly(&G, 4, 2, 3, 4);
            int none[NP]; for (int p = 0; p < NP; p++) none[p] = -1;
            build(&F, &G, none);
            long c = cost_full();
            if (best < 0 || c < best) {
                best = c;
                printf("SCREEN tr %d base cost %ld\n", tr, c);
                printpoly("  F", &F); printpoly("  G", &G);
                fflush(stdout);
            }
        }
        printf("SCREEN_DONE best %ld\n", best);
        return 0;
    }
    int ntr = trials ? trials : ncand;
    for (int tr = 0; tr < ntr; tr++) {
        Poly F, G;
        if (trials == 0) {
            /* fill F,G from candidate table; each term: (c, e_a1, e_b1, e_a2, e_b2) packed in CF/CG cols 0..4 */
            F.n = nF[tr]; for (int t = 0; t < F.n; t++) { F.c[t]=CF[tr][t][0]; F.e[t][0]=CF[tr][t][1]; F.e[t][1]=CF[tr][t][2]; F.e[t][2]=0; F.e[t][3]=0; }
            G.n = nG[tr]; for (int t = 0; t < G.n; t++) { G.c[t]=CG[tr][t][0]; G.e[t][0]=CG[tr][t][1]; G.e[t][1]=CG[tr][t][2]; G.e[t][2]=CG[tr][t][3]; G.e[t][3]=CG[tr][t][4]; }
            /* base cost with no removal */
            for (int p=0;p<NP;p++) {}
            int none[NP]; for (int p=0;p<NP;p++) none[p] = -1;
            build(&F, &G, none);
            printf("CAND %d base(full 7-regular) cost %ld\n", tr, cost_full());
            fflush(stdout);
        } else {
        /* f in (a1,b1) with total degree <= 3; g in (a1,b1,a2,b2) with degree <= 3 */
        int thr = argc > 5 ? atoi(argv[5]) : 800;
        for (int draw = 0;; draw++) {
            randpoly(&F, 3, 3, 3, 2);
            randpoly(&G, 4, 2, 3, 4);
            int none[NP]; for (int p = 0; p < NP; p++) none[p] = -1;
            build(&F, &G, none);
            long bc = cost_full();
            if (bc < thr || draw > 300000) { printf("BASE cost %ld after %d draws\n", bc, draw); break; }
        }
        }
        int rem[NP];
        for (int p = 0; p < NP; p++) rem[p] = rand() % Q;
        build(&F, &G, rem);
        long cur = cost_full();
        int pen = penalty();
        double E = cur + lam * pen;
        long tbest = -1;
        double T0 = 3.0;
        for (int it = 0; it < iters; it++) {
            double T = T0 * (1.0 - (double)it / iters) + 0.05;
            int p = rand() % NP;
            int old = rem[p];
            int nw = (old + 1 + rand() % 6) % Q;
            rem[p] = nw;
            build(&F, &G, rem);
            long c2 = cost_full();
            int pen2 = penalty();
            double E2 = c2 + lam * pen2;
            if (E2 <= E || exp((E - E2) / T) > (double)rand() / RAND_MAX) {
                E = E2; cur = c2; pen = pen2;
                if (pen == 0 && (tbest < 0 || cur < tbest)) tbest = cur;
                if (pen == 0 && (gbest < 0 || cur < gbest)) {
                    gbest = cur;
                    printf("NEWBEST trial %d it %d cost %ld\n", tr, it, cur);
                    fflush(stdout);
                }
                if (pen == 0 && cur == 0) {
                    char path[512];
                    snprintf(path, sizeof path, "%s_s%u_t%d.edges", outp, seed, tr);
                    write_edges(path, rem);
                    printf("VALID_CANDIDATE %s\n", path);
                    fflush(stdout);
                }
            } else {
                rem[p] = old;
            }
        }
        printf("trial %d tbest %ld final cur %ld pen %d\n", tr, tbest, cur, pen);
        printpoly("  F", &F);
        printpoly("  G", &G);
        fflush(stdout);
    }
    printf("GLOBAL_BEST %ld\n", gbest);
    return 0;
}
