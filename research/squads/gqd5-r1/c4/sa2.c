/* Simulated annealing over (M: points->lines bijection, R: freed points) for Q(4,5), criterion (E1)-(E3).
   usage: sa SEED KSTART KMAX ITERS RESTARTS OUTPREFIX */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <stdint.h>
#define N 156
#define D 6
#define C 30
static int L[N][D], PL[N][D], COL[N][C], CON[N][C];
static int M[N], Minv[N], inR[N], R[N], k;
static int OVOID = 0;
#define okR(y) okRn((y), k)
static int okRn(int y, int n){ if (!OVOID) return 1; for (int i = 0; i < n; i++) { int x = R[i]; if (x == y) return 0; for (int j = 0; j < C; j++) if (COL[y][j] == x) return 0; } return 1; }
static uint64_t rs;
static inline uint64_t rnd(void){ rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static inline int ri(int n){ return (int)(rnd() % (uint64_t)n); }
static inline double rd(void){ return (rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int cost(void){
    static int cov[N], covL[N], markL[N];
    int c = 0;
    memset(markL, 0, sizeof markL);
    for (int i = 0; i < k; i++) markL[M[R[i]]] = 1;
    for (int p = 0; p < N; p++) {               /* E1 */
        int cnt = 0;
        for (int j = 0; j < D; j++) cnt += markL[PL[p][j]];
        if (cnt >= D) c++;
    }
    for (int i = 0; i < k; i++) {
        int x = R[i];
        memset(cov, 0, sizeof cov);             /* E2: M(col(x) \ R) covers all points */
        for (int j = 0; j < C; j++) {
            int a = COL[x][j]; if (inR[a]) continue;
            int l = M[a];
            for (int t = 0; t < D; t++) cov[L[l][t]] = 1;
        }
        for (int p = 0; p < N; p++) if (!cov[p]) c++;
        memset(covL, 0, sizeof covL);           /* E3: M^-1(con(M(x))) \ R covers all lines */
        int mx = M[x];
        for (int j = 0; j < C; j++) {
            int a = Minv[CON[mx][j]]; if (inR[a]) continue;
            for (int t = 0; t < D; t++) covL[PL[a][t]] = 1;
        }
        for (int l = 0; l < N; l++) if (!covL[l]) c++;
    }
    return c;
}

static void load(const char *fn){
    FILE *f = fopen(fn, "r");
    int n, m;
    if (fscanf(f, "%d %d", &n, &m) != 2) exit(1);
    for (int l = 0; l < N; l++) for (int t = 0; t < D; t++) { int p; fscanf(f, "%d", &p); L[l][t] = p; }
    /* PL: lines through point, built from L */
    int cntp[N] = {0};
    for (int l = 0; l < N; l++) for (int t = 0; t < D; t++) { int p = L[l][t]; PL[p][cntp[p]++] = l; }
    for (int p = 0; p < N; p++) { int c; fscanf(f, "%d", &c); for (int j = 0; j < c; j++) { int v; fscanf(f, "%d", &v); COL[p][j] = v; } }
    for (int l = 0; l < N; l++) { int c; fscanf(f, "%d", &c); for (int j = 0; j < c; j++) { int v; fscanf(f, "%d", &v); CON[l][j] = v; } }
    fclose(f);
}

static void setR_inR(void){ memset(inR, 0, sizeof inR); for (int i = 0; i < k; i++) inR[R[i]] = 1; }

static void save(const char *prefix, int kk){
    char fn[512]; snprintf(fn, sizeof fn, "%s_k%d.json", prefix, kk);
    FILE *f = fopen(fn, "w");
    fprintf(f, "{\"R\": [");
    for (int i = 0; i < k; i++) fprintf(f, "%s%d", i ? ", " : "", R[i]);
    fprintf(f, "], \"M\": [");
    for (int p = 0; p < N; p++) fprintf(f, "%s%d", p ? ", " : "", M[p]);
    fprintf(f, "]}\n");
    fclose(f);
}

static void randinit(void){
    for (int i = 0; i < N; i++) M[i] = i;
    for (int i = N - 1; i > 0; i--) { int j = ri(i + 1); int t = M[i]; M[i] = M[j]; M[j] = t; }
    for (int p = 0; p < N; p++) Minv[M[p]] = p;
    memset(inR, 0, sizeof inR);
    for (int i = 0; i < k; i++) { int p; do p = ri(N); while (inR[p] || !okRn(p, i)); R[i] = p; inR[p] = 1; }
}

static void addrandom(void){
    int p; do p = ri(N); while (inR[p] || !okR(p));
    R[k++] = p; inR[p] = 1;
}

/* anneal current state for iters steps; returns best cost; state left at best */
static int anneal(long iters, double T0, double T1, int *bestM, int *bestMinv, int *bestR){
    int cur = cost(), best = cur;
    memcpy(bestM, M, sizeof M); memcpy(bestR, R, sizeof(int) * k);
    for (long it = 0; it < iters && best > 0; it++) {
        double T = T0 * pow(T1 / T0, (double)it / iters);
        double u = rd();
        if (u < 0.55) {                       /* swap images of two random points */
            int a = ri(N), b = ri(N); if (a == b) continue;
            int la = M[a], lb = M[b];
            M[a] = lb; M[b] = la; Minv[lb] = a; Minv[la] = b;
            int nc = cost();
            if (nc <= cur || rd() < exp((cur - nc) / T)) { cur = nc; }
            else { M[a] = la; M[b] = lb; Minv[la] = a; Minv[lb] = b; }
        } else if (u < 0.75) {                /* focused swap: a collinear with some x in R */
            int x = R[ri(k)];
            int a = COL[x][ri(C)], b = ri(N); if (a == b) continue;
            int la = M[a], lb = M[b];
            M[a] = lb; M[b] = la; Minv[lb] = a; Minv[la] = b;
            int nc = cost();
            if (nc <= cur || rd() < exp((cur - nc) / T)) { cur = nc; }
            else { M[a] = la; M[b] = lb; Minv[la] = a; Minv[lb] = b; }
        } else if (u < 0.9) {                 /* replace an element of R */
            int i = ri(k), y = ri(N); if (inR[y]) continue; if (!okR(y)) continue;
            int x = R[i];
            R[i] = y; inR[x] = 0; inR[y] = 1;
            int nc = cost();
            if (nc <= cur || rd() < exp((cur - nc) / T)) { cur = nc; }
            else { R[i] = x; inR[y] = 0; inR[x] = 1; }
        } else {                               /* 3-cycle of images */
            int a = ri(N), b = ri(N), c3 = ri(N);
            if (a == b || b == c3 || a == c3) continue;
            int sa = M[a], sb = M[b], sc = M[c3];
            M[a] = sb; M[b] = sc; M[c3] = sa;
            Minv[sb] = a; Minv[sc] = b; Minv[sa] = c3;
            int nc = cost();
            if (nc <= cur || rd() < exp((cur - nc) / T)) { cur = nc; }
            else { M[a] = sa; M[b] = sb; M[c3] = sc; Minv[sa] = a; Minv[sb] = b; Minv[sc] = c3; }
        }
        if (cur < best) {
            best = cur;
            memcpy(bestM, M, sizeof M); memcpy(bestR, R, sizeof(int) * k);
            if (best == 0) break;
        }
    }
    return best;
}

int main(int argc, char **argv){
    if (argc < 7) { fprintf(stderr, "usage: sa SEED KSTART KMAX ITERS RESTARTS OUTPREFIX\n"); return 1; }
    rs = strtoull(argv[1], 0, 10) * 2654435761ULL + 12345; if (!rs) rs = 1;
    int kstart = atoi(argv[2]), kmax = atoi(argv[3]);
    long iters = atol(argv[4]); int restarts = atoi(argv[5]);
    const char *prefix = argv[6];
    if (argc > 7) OVOID = atoi(argv[7]);
    load("/home/user/degree-diameter/research/squads/gqd5-r1/c4/q45.txt");
    static int sM[N], sMinv[N], sR[N], bM[N], bMinv[N], bR[N];
    int have = 0;
    k = kstart; randinit();
    for (int kk = kstart; kk <= kmax; kk++) {
        int solved = 0, bestc = 1 << 30;
        for (int r = 0; r < restarts && !solved; r++) {
            if (have && r % 2 == 0) {          /* extend previous solution by one freed point */
                memcpy(M, sM, sizeof M); memcpy(Minv, sMinv, sizeof Minv); memcpy(R, sR, sizeof(int) * (kk - 1));
                k = kk - 1; setR_inR(); addrandom();
            } else {
                k = kk; randinit();
            }
            int b = anneal(iters, 1.2, 0.05, bM, bMinv, bR);
            if (b < bestc) bestc = b;
            if (b == 0) {
                solved = 1;
                memcpy(M, bM, sizeof M); for (int p = 0; p < N; p++) Minv[M[p]] = p;
                memcpy(R, bR, sizeof(int) * kk); setR_inR();
                save(prefix, kk);
                memcpy(sM, M, sizeof M); memcpy(sMinv, Minv, sizeof Minv); memcpy(sR, R, sizeof(int) * kk);
                have = 1;
            }
            fprintf(stderr, "k=%d restart=%d best=%d %s\n", kk, r, b, b == 0 ? "SOLVED" : "");
        }
        printf("k=%d solved=%d bestcost=%d\n", kk, solved, bestc); fflush(stdout);
        if (!solved) break;
    }
    return 0;
}
