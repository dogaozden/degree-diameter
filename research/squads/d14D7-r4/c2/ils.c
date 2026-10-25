/* ils.c: (1,2)-swap / plateau iterated local search for a larger independent set inside the candidate set
 * C = S u {v not in S : v has at most K orthogonal points in S}. Usage: ils MAP START K SECONDS SEED */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#define Q 11
#define NV 15984
static int X[NV][7], hexid[NV], sline[NV], pt2v[177200];
static int inA[NV], cA[NV];
static inline int orth(int a, int b) {
    int v = X[a][0]*X[b][4] + X[a][4]*X[b][0] + X[a][1]*X[b][5] + X[a][5]*X[b][1] + X[a][2]*X[b][6] + X[a][6]*X[b][2] - 2*X[a][3]*X[b][3];
    v %= Q; if (v < 0) v += Q; return v == 0;
}
static double now(void) { struct timespec ts; clock_gettime(CLOCK_MONOTONIC, &ts); return ts.tv_sec + 1e-9 * ts.tv_nsec; }
static unsigned long long rs = 88172645463325252ULL;
static inline unsigned long long rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int n, *Cv, *dn, **nbl; static unsigned char *am; static int *in, *tight, size_I;
static void addu(int x) { in[x] = 1; size_I++; for (int k = 0; k < dn[x]; k++) tight[nbl[x][k]]++; }
static void remu(int x) { in[x] = 0; size_I--; for (int k = 0; k < dn[x]; k++) tight[nbl[x][k]]--; }
int main(int argc, char **argv) {
    if (argc < 6) { fprintf(stderr, "usage: ils MAP START K SECONDS SEED\n"); return 1; }
    FILE *f = fopen(argv[1], "r"); if (!f) return 1;
    int maxpt = 0;
    for (int i = 0; i < NV; i++) {
        if (fscanf(f, "%d %d", &hexid[i], &sline[i]) != 2) return 1;
        for (int c = 0; c < 7; c++) { int x; if (fscanf(f, "%d", &x) != 1) return 1; x %= Q; if (x < 0) x += Q; X[i][c] = x; }
        if (hexid[i] > maxpt) maxpt = hexid[i];
    }
    fclose(f);
    for (int i = 0; i <= maxpt; i++) pt2v[i] = -1;
    for (int i = 0; i < NV; i++) pt2v[hexid[i]] = i;
    int K = atoi(argv[3]); double secs = atof(argv[4]); rs ^= (unsigned long long)atoll(argv[5]) * 0x2545F4914F6CDD1DULL + 1;
    static int A[NV]; int na = 0; int p, l;
    f = fopen(argv[2], "r"); if (!f) return 1;
    while (fscanf(f, "%d %d", &p, &l) == 2) { int v = pt2v[p]; if (!inA[v]) { inA[v] = 1; A[na++] = v; } }
    fclose(f);
    for (int v = 0; v < NV; v++) if (!inA[v]) for (int i = 0; i < na; i++) if (orth(v, A[i])) cA[v]++;
    Cv = malloc(sizeof(int) * NV); n = 0;
    for (int v = 0; v < NV; v++) if (inA[v] || cA[v] <= K) Cv[n++] = v;
    fprintf(stderr, "candidates n=%d (start %d)\n", n, na);
    am = calloc((size_t)n * n, 1);
    for (int i = 0; i < n; i++) for (int j = 0; j < i; j++) if (orth(Cv[i], Cv[j])) am[(size_t)i*n+j] = am[(size_t)j*n+i] = 1;
    dn = calloc(n, sizeof(int)); nbl = malloc(sizeof(int*) * n);
    for (int i = 0; i < n; i++) { int d = 0; for (int j = 0; j < n; j++) d += am[(size_t)i*n+j]; dn[i] = d; nbl[i] = malloc(sizeof(int) * (d + 1)); d = 0; for (int j = 0; j < n; j++) if (am[(size_t)i*n+j]) nbl[i][d++] = j; }
    in = calloc(n, sizeof(int)); tight = calloc(n, sizeof(int));
    for (int i = 0; i < n; i++) if (inA[Cv[i]]) addu(i);
    fprintf(stderr, "start I=%d (degree in C %d..)\n", size_I, dn[0]);
    int best = size_I; int *Ilist = malloc(sizeof(int) * n), *Lst = malloc(sizeof(int) * n), *Pl = malloc(sizeof(int) * n);
    double t0 = now(); long long it = 0;
    while (now() - t0 < secs) {
        it++;
        int improved = 0;
        int ni = 0; for (int i = 0; i < n; i++) if (in[i]) Ilist[ni++] = i;
        for (int t = ni - 1; t > 0; t--) { int j = rnd() % (t + 1); int tmp = Ilist[t]; Ilist[t] = Ilist[j]; Ilist[j] = tmp; }
        for (int q = 0; q < ni && !improved; q++) {
            int x = Ilist[q], nl = 0;
            for (int k = 0; k < dn[x]; k++) { int u = nbl[x][k]; if (!in[u] && tight[u] == 1) Lst[nl++] = u; }
            for (int a = 0; a < nl && !improved; a++) for (int b = a + 1; b < nl; b++) {
                if (!am[(size_t)Lst[a]*n + Lst[b]]) { remu(x); addu(Lst[a]); addu(Lst[b]); improved = 1; break; }
            }
        }
        if (!improved) {
            int np = 0; for (int i = 0; i < n; i++) if (!in[i] && tight[i] == 1) Pl[np++] = i;
            if (np > 0 && (rnd() % 4) != 0) {
                int u = Pl[rnd() % np]; int x = -1;
                for (int k = 0; k < dn[u]; k++) if (in[nbl[u][k]]) { x = nbl[u][k]; break; }
                remu(x); addu(u);
            } else {
                int u; do { u = rnd() % n; } while (in[u]);
                for (int k = 0; k < dn[u]; k++) if (in[nbl[u][k]]) remu(nbl[u][k]);
                addu(u);
            }
        }
        if (size_I > best) {
            best = size_I;
            fprintf(stderr, "t=%.1f it=%lld I=%d\n", now() - t0, it, best);
            if (best > na) {
                FILE *g = fopen("ils_best.txt", "w");
                for (int i = 0; i < n; i++) if (in[i]) fprintf(g, "%d %d\n", hexid[Cv[i]], sline[Cv[i]]);
                fclose(g);
            }
        }
    }
    /* verify independence of the final set */
    int ok = 1; for (int i = 0; i < n; i++) if (in[i]) for (int j = 0; j < n; j++) if (in[j] && j != i && am[(size_t)i*n+j]) ok = 0;
    printf("candidates %d start %d best I %d final I %d independent %d iterations %lld\n", n, na, best, size_I, ok, it);
    return 0;
}
