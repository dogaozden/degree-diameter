/* hx: exact search for Haar graphs H(G,S), |S| = 4, of diameter <= D (D odd, default 9) in a group G given by a
 * multiplication table, with the search reduced by Aut(G) (the normaliser of the right regular representation).
 *
 * Haar graph: (g,A) ~ (g s, B).  From (e,A) the A-vertices within D-1 are (S S^-1)^h, h = (D-1)/2; from (e,B) the
 * B-vertices within D-1 are (S^-1 S)^h.  Both sides are vertex-transitive, so diam <= D iff both products are G.
 * Cost = #(G \ (S S^-1)^h) + #(G \ (S^-1 S)^h)  (the haar_gen3 / exh3 convention; 0 iff diam <= D).
 *
 * Reductions (all exact):  H(G,S) = H(G, c S d) for c, d in G, so e in S;  H(G,S) = H(G, sigma(S)) for sigma in Aut(G).
 * S = {e, x, y, z}: x runs over Aut-orbit representatives of G \ {e}; y over the orbit representatives of Stab(x)
 * acting on G \ {e, x}; z over all of G \ {e, x, y} (ordered (y,z) pairs, so some sets are evaluated twice; exhaustive).
 *
 * Usage:  hx TABLE AUTGENS LIMIT [D] [XFROM XTO] [OUT]
 *   TABLE: int32 N, then N*N uint16 (row-major, element 0 = identity).  AUTGENS: text, first the count m, then m
 *   permutations of 0..N-1 (generators of Aut(G), or of any subgroup of it: then the search is still exhaustive, only
 *   slower).  LIMIT: report every set with cost <= LIMIT (the search is exact for cost <= LIMIT).  Prints "MIN c" =
 *   the least cost seen if it is <= LIMIT, else "MIN >LIMIT".  XFROM..XTO restrict to a range of x representatives
 *   (for splitting the work).  OUT: file for the hit lines "cost x y z".
 */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <time.h>

static int N, D = 9, H;
static uint16_t *MT; static int *INV;
static int nA; static int **AUT;          /* generators */
static inline int mul(int a, int b) { return MT[(size_t)a * N + b]; }

#define KMAX 64
static int killer[KMAX], nk = 0;
static void kpush(int g) { int i; for (i = 0; i < nk; i++) if (killer[i] == g) break;
    if (i == nk) { if (nk < KMAX) nk++; i = nk - 1; }
    for (; i > 0; i--) killer[i] = killer[i - 1]; killer[0] = g; }

static uint32_t *stamp; static uint32_t cur = 1;
static int Xl[256];
static int req[4096], nreq = 0;   /* HX_REQ: elements that must lie in (SS^-1)^4 and (S^-1S)^4 */

/* X = T^2 as a list with stamp marks; returns |X| */
static int build_X(const int *T, int nt) {
    cur++; if (cur == 0) { memset(stamp, 0, N * 4); cur = 1; }
    int nx = 0;
    for (int i = 0; i < nt; i++) for (int j = 0; j < nt; j++) { int g = mul(T[i], T[j]); if (stamp[g] != cur) { stamp[g] = cur; Xl[nx++] = g; } }
    return nx;
}
/* g in X X ?  iff exists x in X with x^-1 g in X */
static inline int inXX(int g, int nx) { for (int i = 0; i < nx; i++) if (stamp[mul(INV[Xl[i]], g)] == cur) return 1; return 0; }

static uint8_t *cov;
/* full count of G \ X X (h = 4 only), with early exit above lim */
static int miss_full(int nx, int lim, int *missed) {
    memset(cov, 0, N);
    for (int i = 0; i < nx; i++) { const uint16_t *row = MT + (size_t)Xl[i] * N; for (int j = 0; j < nx; j++) cov[row[Xl[j]]] = 1; }
    int m = 0; for (int g = 0; g < N; g++) if (!cov[g]) { if (m < 8) missed[m] = g; m++; if (m > lim) return m; }
    return m;
}
/* general h by BFS (used when D != 9) */
static int miss_bfs(const int *T, int nt, int lim, int *missed) {
    static int *fr = 0, *nxl = 0; if (!fr) { fr = malloc(N * 4); nxl = malloc(N * 4); }
    memset(cov, 0, N); cov[0] = 1; int nf = 1; fr[0] = 0; int tot = 1;
    for (int s = 0; s < H && nf; s++) { int nn = 0;
        for (int i = 0; i < nf; i++) for (int j = 0; j < nt; j++) { int g = mul(fr[i], T[j]); if (!cov[g]) { cov[g] = 1; nxl[nn++] = g; } }
        int *t = fr; fr = nxl; nxl = t; nf = nn; tot += nn; }
    int m = N - tot; if (m > lim) return m;
    int k = 0; for (int g = 0; g < N && k < 8; g++) if (!cov[g]) missed[k++] = g; return m;
}

static long long evals = 0, full = 0;
/* cost of S = {e,x,y,z}; returns > lim if above lim */
static int cost(int x, int y, int z, int lim) {
    int S[4] = {0, x, y, z}; int T1[16], T2[16]; int n1 = 0, n2 = 0;
    for (int i = 0; i < 4; i++) for (int j = 0; j < 4; j++) {
        int a = mul(S[i], INV[S[j]]), b = mul(INV[S[i]], S[j]);
        int k; for (k = 0; k < n1; k++) if (T1[k] == a) break; if (k == n1) T1[n1++] = a;
        for (k = 0; k < n2; k++) if (T2[k] == b) break; if (k == n2) T2[n2++] = b; }
    evals++;
    int missed[8], c = 0;
    if (H == 4) {
        int nx = build_X(T1, n1);
        if (nx * nx < N) return lim + 1;
        for (int i = 0; i < nreq; i++) if (!inXX(req[i], nx)) return lim + 1;
        for (int i = 0; i < nk; i++) if (!inXX(killer[i], nx)) { c++; if (c > lim) { kpush(killer[i]); return lim + 1; } }
        int nx2 = 0, c2 = 0;
        full++;
        int m1 = miss_full(nx, lim, missed); if (m1 > lim) { for (int i = 0; i < (m1 < 8 ? m1 : 8) && i < 2; i++) kpush(missed[i]); return lim + 1; }
        nx2 = build_X(T2, n2);
        if (nx2 * nx2 < N) return lim + 1;
        for (int i = 0; i < nreq; i++) if (!inXX(req[i], nx2)) return lim + 1;
        for (int i = 0; i < nk; i++) if (!inXX(killer[i], nx2)) { c2++; if (m1 + c2 > lim) { kpush(killer[i]); return lim + 1; } }
        int m2 = miss_full(nx2, lim - m1, missed); if (m1 + m2 > lim) { if (m2 > 0) kpush(missed[0]); return lim + 1; }
        return m1 + m2;
    } else {
        int m1 = miss_bfs(T1, n1, lim, missed); if (m1 > lim) { kpush(missed[0]); return lim + 1; }
        int m2 = miss_bfs(T2, n2, lim - m1, missed); if (m1 + m2 > lim) { kpush(missed[0]); return lim + 1; }
        return m1 + m2;
    }
}

/* orbits of a group generated by perms (restricted to those in list 'gens' of size ng) */
static int *orbit_reps(int **gens, int ng, int *nrep, int *orbid) {
    int *rep = malloc(N * 4); int nr = 0; int *q = malloc(N * 4);
    for (int i = 0; i < N; i++) orbid[i] = -1;
    for (int s = 0; s < N; s++) { if (orbid[s] >= 0) continue;
        int h = 0, t = 0; q[t++] = s; orbid[s] = nr;
        while (h < t) { int a = q[h++]; for (int g = 0; g < ng; g++) { int b = gens[g][a]; if (orbid[b] < 0) { orbid[b] = nr; q[t++] = b; } } }
        rep[nr++] = s; }
    free(q); *nrep = nr; return rep;
}

/* stabiliser of x: Schreier generators from the orbit of x under AUT (deduplicated, capped) */
static int **stab_gens(int x, int *ns) {
    /* transversal: for each point in orbit, a perm mapping x to it */
    int *where = malloc(N * 4); for (int i = 0; i < N; i++) where[i] = -1;
    int **tr = malloc(N * sizeof(int *)); int *orb = malloc(N * 4); int no = 0;
    tr[x] = malloc(N * 4); for (int i = 0; i < N; i++) tr[x][i] = i; where[x] = 0; orb[no++] = x;
    for (int h = 0; h < no; h++) { int a = orb[h];
        for (int g = 0; g < nA; g++) { int b = AUT[g][a]; if (where[b] < 0) { where[b] = no; orb[no++] = b;
            tr[b] = malloc(N * 4); for (int i = 0; i < N; i++) tr[b][i] = AUT[g][tr[a][i]]; } } }
    /* Schreier generators tr[g(a)]^-1 * g * tr[a] */
    int cap = 4096; int **sg = malloc(cap * sizeof(int *)); int n = 0;
    int *tinv = malloc(N * 4);
    for (int h = 0; h < no && n < cap; h++) { int a = orb[h];
        for (int g = 0; g < nA && n < cap; g++) { int b = AUT[g][a]; int *tb = tr[b];
            for (int i = 0; i < N; i++) tinv[tb[i]] = i;
            int *p = malloc(N * 4); int id = 1;
            for (int i = 0; i < N; i++) { p[i] = tinv[AUT[g][tr[a][i]]]; if (p[i] != i) id = 0; }
            if (id) { free(p); continue; }
            int dup = 0; for (int k = 0; k < n && !dup; k++) if (!memcmp(sg[k], p, N * 4)) dup = 1;
            if (dup) { free(p); continue; }
            sg[n++] = p; } }
    for (int h = 0; h < no; h++) free(tr[orb[h]]);
    free(tr); free(orb); free(where); free(tinv);
    *ns = n; return sg;
}

int main(int argc, char **argv) {
    if (argc < 4) { fprintf(stderr, "usage: hx TABLE AUTGENS LIMIT [D] [XFROM XTO] [OUT]\n"); return 2; }
    FILE *f = fopen(argv[1], "rb"); int32_t n32; if (!f || fread(&n32, 4, 1, f) != 1) return 2; N = n32;
    MT = malloc((size_t)N * N * 2); if (fread(MT, 2, (size_t)N * N, f) != (size_t)N * N) return 2; fclose(f);
    INV = malloc(N * 4); for (int a = 0; a < N; a++) for (int b = 0; b < N; b++) if (mul(a, b) == 0) { INV[a] = b; break; }
    f = fopen(argv[2], "r"); if (!f || fscanf(f, "%d", &nA) != 1) return 2; AUT = malloc((nA + 1) * sizeof(int *));
    for (int g = 0; g < nA; g++) { AUT[g] = malloc(N * 4); for (int i = 0; i < N; i++) if (fscanf(f, "%d", &AUT[g][i]) != 1) return 3; }
    fclose(f);
    if (nA == 0) { AUT[0] = malloc(N * 4); for (int i = 0; i < N; i++) AUT[0][i] = i; nA = 1; }
    /* sanity: each generator is an automorphism */
    for (int g = 0; g < nA; g++) for (int t = 0; t < 2000; t++) { int a = rand() % N, b = rand() % N;
        if (AUT[g][mul(a, b)] != mul(AUT[g][a], AUT[g][b])) { fprintf(stderr, "generator %d is not an automorphism\n", g); return 4; } }
    int LIM = atoi(argv[3]); if (argc > 4) D = atoi(argv[4]); H = (D - 1) / 2;
    { const char *rq = getenv("HX_REQ"); if (rq) { FILE *g = fopen(rq, "r"); int v; while (g && fscanf(g, "%d", &v) == 1) req[nreq++] = v; if (g) fclose(g);
      fprintf(stderr, "HX_REQ: %d required elements\n", nreq); } }
    stamp = calloc(N, 4); cov = malloc(N);
    int *orbid = malloc(N * 4); int nrep; int *rep = orbit_reps(AUT, nA, &nrep, orbid);
    int xf = 1, xt = nrep - 1; if (argc > 6) { xf = atoi(argv[5]); xt = atoi(argv[6]); if (xt > nrep - 1) xt = nrep - 1; }
    FILE *out = argc > 7 ? fopen(argv[7], "a") : NULL;
    fprintf(stderr, "N=%d D=%d aut gens=%d x-orbits=%d (excluding e), doing reps %d..%d, LIMIT %d\n", N, D, nA, nrep - 1, xf, xt, LIM);
    int best = 1 << 30; long long hits = 0; double t0 = (double)clock() / CLOCKS_PER_SEC;
    int *orb2 = malloc(N * 4);
    for (int ri = xf; ri <= xt; ri++) { int x = rep[ri];
        int ns; int **sg = stab_gens(x, &ns);
        int nr2; int *rep2 = orbit_reps(sg, ns, &nr2, orb2);
        long long e0 = evals;
        for (int k = 0; k < nr2; k++) { int y = rep2[k]; if (y == 0 || y == x) continue;
            for (int z = 0; z < N; z++) { if (z == 0 || z == x || z == y) continue;
                /* each unordered {y,z}: if z's stab-orbit rep is < y's rep index, the set was (or will be) seen with z as y */
                if (orb2[z] < orb2[y]) continue;
                int c = cost(x, y, z, LIM);
                if (c <= LIM) { hits++; if (c < best) best = c; if (out) { fprintf(out, "%d %d %d %d\n", c, x, y, z); fflush(out); }
                    if (c == 0) printf("HIT0 %d %d %d\n", x, y, z); } } }
        fprintf(stderr, "rep %d/%d x=%d stab gens %d y-orbits %d evals %lld best %d t=%.1fs\n", ri, xt, x, ns, nr2, evals - e0,
                best > LIM ? -1 : best, (double)clock() / CLOCKS_PER_SEC - t0);
        for (int i = 0; i < ns; i++) free(sg[i]); free(sg); free(rep2);
    }
    if (best <= LIM) printf("MIN %d hits %lld evals %lld full %lld\n", best, hits, evals, full);
    else printf("MIN >%d evals %lld full %lld\n", LIM, evals, full);
    return 0;
}
