/* a2inv.c: EXHAUSTIVE search over alpha-invariant voltage lifts of the 2+2 base [[a,6-a],[6-a,a]] by a group G, D = 5.
 *
 * Base: A0=0, A1=1 (side 0), B0=2, B1=3 (side 1). Classes: 00 = A0B0 (a edges), 01 = A0B1 (6-a), 10 = A1B0 (6-a),
 * 11 = A1B1 (a). Lift vertex (v,h), base edge (u,w,g): (u,h) ~ (w,h*g). A class voltage set S must be a SET (distinct
 * voltages, else multi-edges) and alpha-invariant: then (v,h) -> (v,alpha(h)) is an automorphism of the lift fixing
 * every fibre. Tree normalisation (default): 1 in S for classes 00, 01, 11 (A0B0, A0B1, A1B1 form a spanning tree);
 * class 10 is free. NOTREE=1 drops that constraint (a strictly larger family, still a valid lift family).
 * Each S is a union of alpha-orbits of the right total size; all combinations are enumerated.
 * Cost = number of uncovered (v,h) pairs over the 4 base sources (vl.c convention); 0 <=> diameter <= 5.
 *
 * usage: a2inv GROUPFILE ALPHAFILE A       (GROUPFILE: m then m rows; ALPHAFILE: "order classsize m" then perm)
 * env: COUNT=1 (print candidate counts and exit), OUT=sol.txt (vl format, best solution), NOTREE=1, LIMIT=cost to
 *      stop early once a configuration with cost <= LIMIT is found (default 0)
 */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXM 256
#define MAXS 400000
#define NV 4
static int m;
static uint16_t mul[MAXM][MAXM];
static int inv_[MAXM], alpha[MAXM];
static int orb_of[MAXM], norb, orb_el[MAXM][MAXM], orb_sz[MAXM];
static const int side[NV] = {0, 0, 1, 1};
static int a_, notree;
static int csz[4], cu[4] = {0, 0, 1, 1}, cw[4] = {2, 3, 2, 3}, cneed[4];
static int cbase[4];                    /* first edge index of class */
static int cand[4][MAXS][6]; static int ncand[4];
static int eu[12], ew[12], volt[12];
static int deg[NV], dn[NV][6], de[NV][6], dd[NV][6];
static unsigned char cov[NV][MAXM];
static int maxlen_;

static void dfs(int v, int laste, int h, int len) {
    cov[v][h] = 1;
    if (len == maxlen_) return;
    for (int i = 0; i < deg[v]; i++) {
        int e = de[v][i]; if (e == laste) continue;
        int g = volt[e]; if (dd[v][i]) g = inv_[g];
        dfs(dn[v][i], e, mul[h][g], len + 1);
    }
}
/* lift cost, abort (return > limit) when the partial sum exceeds limit */
static long cost(long limit) {
    memset(deg, 0, sizeof deg);
    for (int e = 0; e < 12; e++) {
        int u = eu[e], w = ew[e];
        dn[u][deg[u]] = w; de[u][deg[u]] = e; dd[u][deg[u]] = 0; deg[u]++;
        dn[w][deg[w]] = u; de[w][deg[w]] = e; dd[w][deg[w]] = 1; deg[w]++;
    }
    long c = 0;
    for (int s = 0; s < NV; s++) {
        memset(cov, 0, sizeof cov);
        maxlen_ = side[s] == 0 ? 5 : 4;
        dfs(s, -1, 0, 0);
        for (int v = 0; v < NV; v++) {
            if (side[s] == 1 && side[v] == 0) continue;
            for (int h = 0; h < m; h++) if (!cov[v][h]) c++;
        }
        if (c > limit) return c;
    }
    return c;
}

static int tmpset[6], ntmp;
static int target;     /* elements still needed */
static int cls;
static void gen(int j, int need) {
    if (need == 0) { if (ncand[cls] >= MAXS) { fprintf(stderr, "MAXS\n"); exit(3); }
        memcpy(cand[cls][ncand[cls]], tmpset, sizeof(int) * 6); ncand[cls]++; return; }
    for (int o = j; o < norb; o++) {
        if (orb_sz[o] > need) continue;
        if (cneed[cls] && o == 0) continue;               /* identity orbit handled separately */
        int save = ntmp;
        for (int k = 0; k < orb_sz[o]; k++) tmpset[ntmp++] = orb_el[o][k];
        gen(o + 1, need - orb_sz[o]);
        ntmp = save;
    }
}

static int readgroup(const char *path) {
    FILE *f = fopen(path, "r"); if (!f) { perror(path); exit(1); }
    if (fscanf(f, "%d", &m) != 1 || m > MAXM) exit(1);
    for (int i = 0; i < m; i++) for (int j = 0; j < m; j++) { int x; if (fscanf(f, "%d", &x) != 1) exit(1); mul[i][j] = x; }
    fclose(f); return m;
}

int main(int argc, char **argv) {
    if (argc < 4) { fprintf(stderr, "usage: a2inv GROUP ALPHA A\n"); return 1; }
    readgroup(argv[1]);
    a_ = atoi(argv[3]);
    notree = getenv("NOTREE") && atoi(getenv("NOTREE"));
    long limit = getenv("LIMIT") ? atol(getenv("LIMIT")) : 0;
    int countonly = getenv("COUNT") && atoi(getenv("COUNT"));
    /* identity is 0; inverses */
    for (int i = 0; i < m; i++) for (int j = 0; j < m; j++) if (mul[i][j] == 0) inv_[i] = j;
    /* alpha */
    FILE *fa = fopen(argv[2], "r"); if (!fa) { perror(argv[2]); return 1; }
    int ord, csize, mm; if (fscanf(fa, "%d %d %d", &ord, &csize, &mm) != 3 || mm != m) { fprintf(stderr, "alpha m mismatch\n"); return 1; }
    for (int i = 0; i < m; i++) if (fscanf(fa, "%d", &alpha[i]) != 1) return 1;
    fclose(fa);
    /* check automorphism and bijection */
    { static int seen[MAXM]; memset(seen, 0, sizeof seen);
      for (int i = 0; i < m; i++) { if (seen[alpha[i]]) { fprintf(stderr, "not bijective\n"); return 1; } seen[alpha[i]] = 1; }
      for (int i = 0; i < m; i++) for (int j = 0; j < m; j++) if (alpha[mul[i][j]] != mul[alpha[i]][alpha[j]]) { fprintf(stderr, "not an automorphism\n"); return 1; } }
    if (alpha[0] != 0) { fprintf(stderr, "alpha(1) != 1\n"); return 1; }
    /* orbits; identity orbit first */
    memset(orb_of, -1, sizeof orb_of); norb = 0;
    for (int x = 0; x < m; x++) {
        if (orb_of[x] >= 0) continue;
        int y = x, k = 0;
        do { orb_of[y] = norb; orb_el[norb][k++] = y; y = alpha[y]; } while (y != x);
        orb_sz[norb] = k; norb++;
    }
    int nfix = 0; for (int o = 0; o < norb; o++) if (orb_sz[o] == 1) nfix++;
    /* class sizes */
    csz[0] = a_; csz[1] = 6 - a_; csz[2] = 6 - a_; csz[3] = a_;
    for (int c = 0; c < 4; c++) cneed[c] = (!notree) && (c != 2);
    cbase[0] = 0; cbase[1] = csz[0]; cbase[2] = csz[0] + csz[1]; cbase[3] = cbase[2] + csz[2];
    /* enumerate candidate sets per class: union of orbits, total size csz; identity orbit forced when cneed */
    for (cls = 0; cls < 4; cls++) {
        ncand[cls] = 0; ntmp = 0;
        if (cneed[cls]) { tmpset[ntmp++] = 0; gen(1, csz[cls] - 1); }
        else gen(0, csz[cls]);
    }
    double space = (double)ncand[0] * ncand[1] * ncand[2] * ncand[3];
    fprintf(stderr, "m=%d alpha order=%d |Fix|=%d orbits=%d a=%d notree=%d cands: %d %d %d %d  configs=%.0f\n",
            m, ord, nfix, norb, a_, notree, ncand[0], ncand[1], ncand[2], ncand[3], space);
    if (countonly) return 0;
    long best = -1; long nev = 0; int bi[4] = {0, 0, 0, 0};
    clock_t t0 = clock();
    int idx[4];
    for (idx[0] = 0; idx[0] < ncand[0]; idx[0]++)
    for (idx[1] = 0; idx[1] < ncand[1]; idx[1]++)
    for (idx[2] = 0; idx[2] < ncand[2]; idx[2]++)
    for (idx[3] = 0; idx[3] < ncand[3]; idx[3]++) {
        int e = 0;
        for (int c = 0; c < 4; c++) for (int k = 0; k < csz[c]; k++) {
            eu[e] = cu[c]; ew[e] = cw[c]; volt[e] = cand[c][idx[c]][k]; e++; }
        long lim = best < 0 ? (long)1 << 40 : best - 1;   /* only strictly better configs matter */
        long cc = cost(lim); nev++;
        if (best < 0 || cc < best) {
            if (best < 0 || cc <= lim) {
                best = cc; memcpy(bi, idx, sizeof bi);
                if (best <= limit) goto done;
            }
        }
    }
done:
    fprintf(stderr, "evaluated %ld configs in %.1fs\n", nev, (double)(clock() - t0) / CLOCKS_PER_SEC);
    /* recompute best and write */
    {
        int e = 0;
        for (int c = 0; c < 4; c++) for (int k = 0; k < csz[c]; k++) {
            eu[e] = cu[c]; ew[e] = cw[c]; volt[e] = cand[c][bi[c]][k]; e++; }
        long cc = cost(1L << 40);
        printf("RESULT best %ld m=%d a=%d alpha_order=%d fix=%d notree=%d\n", cc, m, a_, ord, nfix, notree);
        const char *out = getenv("OUT");
        if (out) {
            FILE *f = fopen(out, "w");
            fprintf(f, "4 12\n0 0 1 1\n");
            for (int i = 0; i < 12; i++) fprintf(f, "%d %d %d\n", eu[i], ew[i], volt[i]);
            fclose(f);
        }
    }
    return 0;
}
