/* Port of gqd5-r1/c4/sa.c to any GQ of order (q,q) given as a graph file (see mkgraph.py).
   Criterion (E1)-(E3) of Theorem E for an H->H transition (A = points, B = lines), M: points -> lines bijection.
   usage: sa_gen GRAPH SEED KSTART KMAX ITERS RESTARTS OUTPREFIX [INITFILE]
   INITFILE (optional, first restart of KSTART only): "R r1 .. rk" line then "M m0 .. m_{N-1}" line.
   Writes OUTPREFIX_k<k>.json = {"R": [...], "M": [...]} for each solved k. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <stdint.h>
#define MAXN 1024
#define MAXD 12
#define MAXC 112
static int N, D, C;
static int L[MAXN][MAXD], PL[MAXN][MAXD], COL[MAXN][MAXC], CON[MAXN][MAXC];
static int M[MAXN], Minv[MAXN], inR[MAXN], R[MAXN], k;
static uint64_t rs;
static inline uint64_t rnd(void){ rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static inline int ri(int n){ return (int)(rnd() % (uint64_t)n); }
static inline double rd(void){ return (rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int cost(void){
    static int cov[MAXN], covL[MAXN], markL[MAXN];
    int c = 0;
    if (k >= D) {                                /* E1 (only possible when k >= q+1) */
        memset(markL, 0, sizeof markL);
        for (int i = 0; i < k; i++) markL[M[R[i]]] = 1;
        for (int p = 0; p < N; p++) {
            int cnt = 0;
            for (int j = 0; j < D; j++) cnt += markL[PL[p][j]];
            if (cnt >= D) c++;
        }
    }
    for (int i = 0; i < k; i++) {
        int x = R[i];
        memset(cov, 0, sizeof cov);              /* E2: M(col(x) \ R) covers all points */
        for (int j = 0; j < C; j++) {
            int a = COL[x][j]; if (inR[a]) continue;
            int l = M[a];
            for (int t = 0; t < D; t++) cov[L[l][t]] = 1;
        }
        for (int p = 0; p < N; p++) if (!cov[p]) c++;
        memset(covL, 0, sizeof covL);            /* E3: M^-1(con(M(x))) \ R covers all lines */
        int mx = M[x];
        for (int j = 0; j < C; j++) {
            int a = Minv[CON[mx][j]]; if (inR[a]) continue;
            for (int t = 0; t < D; t++) covL[PL[a][t]] = 1;
        }
        for (int l = 0; l < N; l++) if (!covL[l]) c++;
    }
    return c;
}


static void loadg(const char *fn){
    FILE *f = fopen(fn, "r");
    if (!f) { perror(fn); exit(1); }
    char buf[1 << 16];
    if (!fgets(buf, sizeof buf, f)) exit(1);
    int n, m; sscanf(buf, "%d %d", &n, &m); N = n;
    /* first line of blocks: D = number of tokens in line 1 */
    if (!fgets(buf, sizeof buf, f)) exit(1);
    D = 0; { char *s = buf; int v, nch; while (sscanf(s, "%d%n", &v, &nch) == 1) { D++; s += nch; } }
    rewind(f);
    if (!fgets(buf, sizeof buf, f)) exit(1);
    int cntp[MAXN]; memset(cntp, 0, sizeof cntp);
    for (int l = 0; l < N; l++) for (int t = 0; t < D; t++) { if (fscanf(f, "%d", &L[l][t]) != 1) exit(1); }
    for (int l = 0; l < N; l++) for (int t = 0; t < D; t++) { int p = L[l][t]; PL[p][cntp[p]++] = l; }
    C = 0;
    for (int p = 0; p < N; p++) { int c; fscanf(f, "%d", &c); if (c > C) C = c; for (int j = 0; j < c; j++) { int v; fscanf(f, "%d", &v); COL[p][j] = v; } }
    for (int l = 0; l < N; l++) { int c; fscanf(f, "%d", &c); for (int j = 0; j < c; j++) { int v; fscanf(f, "%d", &v); CON[l][j] = v; } }
    fclose(f);
    fprintf(stderr, "graph N=%d D=%d C=%d\n", N, D, C);
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
    for (int i = 0; i < k; i++) { int p; do p = ri(N); while (inR[p]); R[i] = p; inR[p] = 1; }
}

static void readinit(const char *fn){
    FILE *f = fopen(fn, "r"); if (!f) { perror(fn); exit(1); }
    char tag[8];
    fscanf(f, "%7s", tag); /* R */
    k = 0; int v;
    /* read R until 'M' token */
    long pos;
    while (1) {
        pos = ftell(f);
        if (fscanf(f, "%d", &v) != 1) break;
        R[k++] = v;
    }
    fseek(f, pos, SEEK_SET); fscanf(f, "%7s", tag);
    for (int p = 0; p < N; p++) { if (fscanf(f, "%d", &M[p]) != 1) { fprintf(stderr, "bad init\n"); exit(1); } }
    for (int p = 0; p < N; p++) Minv[M[p]] = p;
    setR_inR();
    fclose(f);
}

static void addrandom(void){
    int p; do p = ri(N); while (inR[p]);
    R[k++] = p; inR[p] = 1;
}

static int anneal(long iters, double T0, double T1, int *bestM, int *bestR){
    int cur = cost(), best = cur;
    memcpy(bestM, M, sizeof(int) * N); memcpy(bestR, R, sizeof(int) * k);
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
            int i = ri(k), y = ri(N); if (inR[y]) continue;
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
            memcpy(bestM, M, sizeof(int) * N); memcpy(bestR, R, sizeof(int) * k);
            if (best == 0) break;
        }
    }
    return best;
}

int main(int argc, char **argv){
    if (argc < 8) { fprintf(stderr, "usage: sa_gen GRAPH SEED KSTART KMAX ITERS RESTARTS OUTPREFIX [INITFILE]\n"); return 1; }
    loadg(argv[1]);
    rs = strtoull(argv[2], 0, 10) * 2654435761ULL + 12345; if (!rs) rs = 1;
    int kstart = atoi(argv[3]), kmax = atoi(argv[4]);
    long iters = atol(argv[5]); int restarts = atoi(argv[6]);
    const char *prefix = argv[7];
    static int sM[MAXN], sR[MAXN], bM[MAXN], bR[MAXN];
    int have = 0;
    k = kstart; randinit();
    if (argc > 8) { readinit(argv[8]); fprintf(stderr, "init from %s, k=%d\n", argv[8], k); have = 2; }
    for (int kk = kstart; kk <= kmax; kk++) {
        int solved = 0, bestc = 1 << 30;
        for (int r = 0; r < restarts && !solved; r++) {
            if (have == 2 && r == 0 && kk == kstart) {
                /* keep init state */
            } else if (have == 1 && r % 2 == 0) {  /* extend previous solution by one freed point */
                memcpy(M, sM, sizeof(int) * N); memcpy(R, sR, sizeof(int) * (kk - 1));
                for (int p = 0; p < N; p++) Minv[M[p]] = p;
                k = kk - 1; setR_inR(); addrandom();
            } else {
                k = kk; randinit();
            }
            int b = anneal(iters, 1.2, 0.05, bM, bR);
            if (b < bestc) bestc = b;
            if (b == 0) {
                solved = 1;
                memcpy(M, bM, sizeof(int) * N); for (int p = 0; p < N; p++) Minv[M[p]] = p;
                memcpy(R, bR, sizeof(int) * kk); k = kk; setR_inR();
                save(prefix, kk);
                memcpy(sM, M, sizeof(int) * N); memcpy(sR, R, sizeof(int) * kk);
                have = 1;
            }
            fprintf(stderr, "k=%d restart=%d best=%d %s\n", kk, r, b, b == 0 ? "SOLVED" : "");
        }
        printf("k=%d solved=%d bestcost=%d\n", kk, solved, bestc); fflush(stdout);
        if (!solved) break;
    }
    return 0;
}
