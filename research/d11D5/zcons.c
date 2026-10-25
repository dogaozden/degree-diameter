/* zcons.c: exact constraint extraction for a lift by G = (Z_K quotient) . Z2 of a base multigraph whose edges carry
   a fixed element of G and possibly a free Z2 variable in the subgroup N = Z2.  (Format: mkbase.py.)
   Diameter <= 5 of the lift <=> for every base source s, target t and coset c in Z_K, the walks of length <= 5
   (<= 4 same side) from s to t with quotient value c do not all have the same N-value.  Each walk's N-value is a
   constant plus an XOR of variables.  Per group (s,t,c), after merging walks with equal (constant, variable set):
   1 class -> FATAL; 2 classes -> one linear equation over GF(2); >= 3 classes -> an OR-constraint (stored if small).
   Then Gaussian elimination decides whether the equations are consistent; if so, writes a particular solution and
   a nullspace basis, and counts violated OR-constraints at random points of the solution space.
   usage: zcons base.txt [outprefix]   env: SEED, MAXOR (default 8), SOURCES (only first n sources) */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
static uint64_t rs = 88172645463325252ULL;
static inline uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
int V, NV, MODE, K, NE;
int *eu, *ev, *efx, *evar;
int *aoff, *anb, *afx, *avar, *aeid;
static inline int gadd(int a, int b) { if (MODE == 0) return ((a % K + b % K) % K) + K * ((a / K) ^ (b / K)); return (a + b) % (2 * K); }
static inline int gneg(int a) { if (MODE == 0) return ((K - a % K) % K) + K * (a / K); return (2 * K - a) % (2 * K); }
typedef struct { int t; uint8_t c, nb, nv; int v[5]; } rec_t;
rec_t *recs; long nrec, caprec;
int path_vars[8], npv;
static void rec(int t, int e) {
    if (nrec == caprec) { caprec *= 2; recs = realloc(recs, caprec * sizeof(rec_t)); }
    rec_t *r = &recs[nrec++]; r->t = t; r->c = e % K; r->nb = e / K; r->nv = npv;
    int tmp[8]; memcpy(tmp, path_vars, npv * sizeof(int));
    for (int i = 1; i < npv; i++) { int x = tmp[i], j = i - 1; while (j >= 0 && tmp[j] > x) { tmp[j + 1] = tmp[j]; j--; } tmp[j + 1] = x; }
    memcpy(r->v, tmp, npv * sizeof(int));
}
static void toggle(int var) { if (var < 0) return; for (int i = 0; i < npv; i++) if (path_vars[i] == var) { path_vars[i] = path_vars[--npv]; return; } path_vars[npv++] = var; }
static void dfs(int x, int e, int last, int d) {
    rec(x, e);
    if (d == 5) return;
    for (int j = aoff[x]; j < aoff[x + 1]; j++) {
        if (aeid[j] == last) continue;
        toggle(avar[j]); dfs(anb[j], gadd(e, afx[j]), aeid[j], d + 1); toggle(avar[j]);
    }
}
static int cmprec(const void *A, const void *B) {
    const rec_t *a = A, *b = B; int ka = a->t * K + a->c, kb = b->t * K + b->c; if (ka != kb) return ka - kb;
    if (a->nv != b->nv) return a->nv - b->nv; for (int i = 0; i < a->nv; i++) if (a->v[i] != b->v[i]) return a->v[i] - b->v[i];
    return a->nb - b->nb;
}
static int samevars(const rec_t *a, const rec_t *b) { if (a->nv != b->nv) return 0; for (int i = 0; i < a->nv; i++) if (a->v[i] != b->v[i]) return 0; return 1; }
/* equations */
int *eqv; int *eqoff; uint8_t *eqrhs; long neq, capeq, capeqv, neqv;
int *eqms, *eqmt; uint8_t *eqmc, *eqmd; int cur_s, cur_d; int *bdist;
static void add_eq(const rec_t *a, const rec_t *b) {
    int tmp[10], n = 0;
    for (int i = 0; i < a->nv; i++) tmp[n++] = a->v[i];
    for (int i = 0; i < b->nv; i++) { int f = -1; for (int j = 0; j < n; j++) if (tmp[j] == b->v[i]) f = j; if (f >= 0) tmp[f] = tmp[--n]; else tmp[n++] = b->v[i]; }
    uint8_t rhs = 1 ^ a->nb ^ b->nb;
    if (n == 0) { if (rhs) { fprintf(stderr, "internal: empty equation with rhs 1 should have been FATAL\n"); } return; }
    if (neq + 2 > capeq) { capeq *= 2; eqoff = realloc(eqoff, (capeq + 1) * sizeof(int)); eqrhs = realloc(eqrhs, capeq);
        eqms = realloc(eqms, capeq * 4); eqmt = realloc(eqmt, capeq * 4); eqmc = realloc(eqmc, capeq); eqmd = realloc(eqmd, capeq); }
    eqms[neq] = cur_s; eqmt[neq] = a->t; eqmc[neq] = a->c; eqmd[neq] = bdist[a->t];
    if (neqv + n > capeqv) { capeqv *= 2; eqv = realloc(eqv, capeqv * sizeof(int)); }
    memcpy(eqv + neqv, tmp, n * sizeof(int)); neqv += n; eqrhs[neq] = rhs; neq++; eqoff[neq] = neqv;
}
/* OR constraints: list of classes (nb + vars) */
typedef struct { uint8_t nb, nv; int v[5]; } cls_t;
cls_t *orc; int *oroff; long nor, caporc, capor, norc;
int main(int argc, char **argv) {
    if (getenv("SEED")) { rs ^= (uint64_t)atoll(getenv("SEED")) * 0x9E3779B97F4A7C15ULL; for (int i = 0; i < 20; i++) rnd(); }
    int MAXOR = getenv("MAXOR") ? atoi(getenv("MAXOR")) : 8;
    FILE *f = fopen(argv[1], "r"); if (fscanf(f, "%d %d %d %d", &V, &NV, &MODE, &K) != 4) return 1;
    int cap = 1 << 16; eu = malloc(cap * 4); ev = malloc(cap * 4); efx = malloc(cap * 4); evar = malloc(cap * 4); NE = 0;
    int a, b, c, d;
    while (fscanf(f, "%d %d %d %d", &a, &b, &c, &d) == 4) { if (NE == cap) { cap *= 2; eu = realloc(eu, cap * 4); ev = realloc(ev, cap * 4); efx = realloc(efx, cap * 4); evar = realloc(evar, cap * 4); } eu[NE] = a; ev[NE] = b; efx[NE] = c; evar[NE] = d; NE++; }
    fclose(f);
    int *deg = calloc(V, 4); for (int i = 0; i < NE; i++) { deg[eu[i]]++; deg[ev[i]]++; }
    aoff = malloc((V + 1) * 4); aoff[0] = 0; for (int i = 0; i < V; i++) aoff[i + 1] = aoff[i] + deg[i];
    anb = malloc(2 * NE * 4); afx = malloc(2 * NE * 4); avar = malloc(2 * NE * 4); aeid = malloc(2 * NE * 4); int *fill = calloc(V, 4);
    for (int i = 0; i < NE; i++) { int x = eu[i], y = ev[i];
        int j = aoff[x] + fill[x]++; anb[j] = y; afx[j] = efx[i]; avar[j] = evar[i]; aeid[j] = i;
        j = aoff[y] + fill[y]++; anb[j] = x; afx[j] = gneg(efx[i]); avar[j] = evar[i]; aeid[j] = i; }
    int maxdeg = 0; for (int i = 0; i < V; i++) if (deg[i] > maxdeg) maxdeg = deg[i];
    printf("base V=%d E=%d maxdeg=%d vars=%d mode=%d K=%d (lift order %d)\n", V, NE, maxdeg, NV, MODE, K, 2 * K * V); fflush(stdout);
    caprec = 1 << 18; recs = malloc(caprec * sizeof(rec_t));
    capeq = 1 << 16; eqoff = malloc((capeq + 1) * sizeof(int)); eqoff[0] = 0; eqrhs = malloc(capeq);
    eqms = malloc(capeq * 4); eqmt = malloc(capeq * 4); eqmc = malloc(capeq); eqmd = malloc(capeq); bdist = malloc(V * 4);
    const char *dsel = getenv("EQDIST");  /* e.g. "0,2,4": keep only equations with these base distances */
    int keepd[16]; for (int i = 0; i < 16; i++) keepd[i] = dsel ? 0 : 1; if (dsel) for (const char *p = dsel; *p; p++) if (*p >= '0' && *p <= '9') keepd[*p - '0'] = 1; capeqv = 1 << 20; eqv = malloc(capeqv * 4); neq = 0; neqv = 0;
    capor = 1 << 16; oroff = malloc((capor + 1) * sizeof(int)); oroff[0] = 0; caporc = 1 << 20; orc = malloc(caporc * sizeof(cls_t)); nor = 0; norc = 0;
    long fatal = 0, nzero = 0, nalways = 0, nbig = 0, groups = 0; long fatal_same = 0, fatal_opp = 0;
    int nsrc = getenv("SOURCES") ? atoi(getenv("SOURCES")) : V;
    FILE *dumpf = getenv("DUMPUNREACHED") ? fopen(getenv("DUMPUNREACHED"), "w") : NULL;
    int stopafter = getenv("STRUCTONLY") != NULL; int dedup = getenv("DEDUP") != NULL;
    int half = V / 2;
    for (int s = 0; s < nsrc; s++) {
        nrec = 0; npv = 0; dfs(s, 0, -1, 0); cur_s = s;
        { for (int t = 0; t < V; t++) bdist[t] = -1; int *qq = malloc(V * 4), qh = 0, qt = 0; bdist[s] = 0; qq[qt++] = s;
          while (qh < qt) { int x = qq[qh++]; for (int j = aoff[x]; j < aoff[x + 1]; j++) if (bdist[anb[j]] < 0) { bdist[anb[j]] = bdist[x] + 1; qq[qt++] = anb[j]; } } free(qq); }
        qsort(recs, nrec, sizeof(rec_t), cmprec);
        /* groups: every (t, c) must appear; check missing groups */
        long i = 0; uint8_t *seen = calloc((size_t)V * K, 1);
        while (i < nrec) {
            long j = i; int key = recs[i].t * K + recs[i].c; while (j < nrec && recs[j].t * K + recs[j].c == key) j++;
            seen[key] = 1; groups++;
            /* unique classes */
            rec_t *u[64]; int nu = 0, always = 0;
            for (long k = i; k < j; k++) {
                if (k > i && samevars(&recs[k], &recs[k - 1]) && recs[k].nb == recs[k - 1].nb) continue;
                if (k > i && samevars(&recs[k], &recs[k - 1]) && recs[k].nb != recs[k - 1].nb) always = 1;
                if (nu < 64) u[nu++] = &recs[k]; else always = 1;   /* huge group: treat as fine (counted below) */
            }
            if (always) nalways++;
            else if (nu == 1) { if (dumpf) fprintf(dumpf, "F %d %d %d %d\n", s, recs[i].t, recs[i].c, bdist[recs[i].t]); fatal++; if ((s < half) == (recs[i].t < half)) fatal_same++; else fatal_opp++; }
            else if (dedup && recs[i].t < s) { /* duplicate of the reversed group */ }
            else if (nu == 2) { if (keepd[bdist[recs[i].t]]) add_eq(u[0], u[1]); }
            else if (nu <= MAXOR) {
                if (nor + 2 > capor) { capor *= 2; oroff = realloc(oroff, (capor + 1) * sizeof(int)); }
                if (norc + nu > caporc) { caporc *= 2; orc = realloc(orc, caporc * sizeof(cls_t)); }
                for (int k = 0; k < nu; k++) { orc[norc].nb = u[k]->nb; orc[norc].nv = u[k]->nv; memcpy(orc[norc].v, u[k]->v, sizeof(int) * 5); norc++; }
                nor++; oroff[nor] = norc;
            } else nbig++;
            i = j;
        }
        /* targets never reached at some coset: walks must reach every (t, c) with t of the right side */
        for (int t = 0; t < V; t++) for (int cc = 0; cc < K; cc++) if (!seen[t * K + cc]) { nzero++; if (dumpf) fprintf(dumpf, "%d %d %d %d\n", s, t, cc, bdist[t]); }
        free(seen);
    }
    if (dumpf) fclose(dumpf);
    printf("groups=%ld unreached(t,coset)=%ld FATAL(one class)=%ld [same side %ld, opposite %ld] always-ok=%ld equations=%ld OR-constraints=%ld big=%ld\n",
           groups, nzero, fatal, fatal_same, fatal_opp, nalways, neq, nor, nbig); fflush(stdout);
    if (nzero || fatal) { printf("STRUCTURE FAILS (some lifted pair is unreachable whatever the variables)\n"); }
    if (neq == 0) { printf("no equations\n"); }
    if (stopafter) return 0;
    /* Gaussian elimination, random order */
    int W = (NV + 63) / 64;
    uint64_t **piv = calloc(NV, sizeof(uint64_t *)); uint8_t *pivrhs = calloc(NV, 1); int rank = 0; long contra = -1;
    long *ord = malloc(neq * sizeof(long)); for (long e = 0; e < neq; e++) ord[e] = e;
    for (long e = neq - 1; e > 0; e--) { long r = rnd() % (e + 1); long t = ord[e]; ord[e] = ord[r]; ord[r] = t; }
    uint64_t *row = malloc(W * 8); long dep = 0;
    int PW = 128; uint64_t **pprov = calloc(NV, sizeof(uint64_t *)); uint64_t *prov = malloc(PW * 8);
    for (long oi = 0; oi < neq; oi++) {
        long e = ord[oi]; memset(row, 0, W * 8); uint8_t rhs = eqrhs[e]; memset(prov, 0, PW * 8); if (oi < PW * 64) prov[oi >> 6] |= 1ULL << (oi & 63);
        for (int k = eqoff[e]; k < eqoff[e + 1]; k++) row[eqv[k] >> 6] ^= 1ULL << (eqv[k] & 63);
        int w = 0;
        while (1) {
            while (w < W && !row[w]) w++;
            if (w == W) { if (rhs) contra = oi; else dep++; break; }
            int bcol = w * 64 + __builtin_ctzll(row[w]);
            if (piv[bcol]) { uint64_t *p = piv[bcol]; for (int k = w; k < W; k++) row[k] ^= p[k]; rhs ^= pivrhs[bcol]; for (int k = 0; k < PW; k++) prov[k] ^= pprov[bcol][k]; }
            else { piv[bcol] = malloc(W * 8); memcpy(piv[bcol], row, W * 8); pivrhs[bcol] = rhs; pprov[bcol] = malloc(PW * 8); memcpy(pprov[bcol], prov, PW * 8); rank++; break; }
        }
        if (contra >= 0) break;
        if ((oi & ((1 << 18) - 1)) == 0 && oi) { printf("  eq %ld rank %d\n", oi, rank); fflush(stdout); }
    }
    if (contra >= 0) { printf("INCONSISTENT after %ld equations (rank %d)\n", contra + 1, rank);
        if (contra < PW * 64) { int cntp = 0; for (long oi = 0; oi <= contra; oi++) if ((prov[oi >> 6] >> (oi & 63)) & 1) cntp++;
            printf("contradiction uses %d equations:\n", cntp);
            for (long oi = 0; oi <= contra; oi++) if ((prov[oi >> 6] >> (oi & 63)) & 1) { long e = ord[oi];
                printf("  s=%d t=%d coset=%d dist=%d rhs=%d vars:", eqms[e], eqmt[e], eqmc[e], eqmd[e], eqrhs[e]);
                for (int k = eqoff[e]; k < eqoff[e + 1]; k++) printf(" %d", eqv[k]); printf("\n"); } }
        return 0; }
    printf("CONSISTENT: equations=%ld rank=%d nullity=%d\n", neq, rank, NV - rank); fflush(stdout);
    /* back substitution: particular solution with free vars = 0, and nullspace basis */
    uint8_t *x0 = calloc(NV, 1);
    for (int col = NV - 1; col >= 0; col--) if (piv[col]) { int s = pivrhs[col]; uint64_t *p = piv[col];
        for (int k = col + 1; k < NV; k++) if ((p[k >> 6] >> (k & 63)) & 1) s ^= x0[k]; x0[col] = s; }
    int nfree = NV - rank; int *freec = malloc(nfree * 4); int nf = 0; for (int col = 0; col < NV; col++) if (!piv[col]) freec[nf++] = col;
    uint8_t **nsb = malloc(nfree * sizeof(uint8_t *));
    for (int i = 0; i < nfree; i++) { uint8_t *x = calloc(NV, 1); x[freec[i]] = 1;
        for (int col = NV - 1; col >= 0; col--) if (piv[col]) { int s = 0; uint64_t *p = piv[col]; for (int k = col + 1; k < NV; k++) if ((p[k >> 6] >> (k & 63)) & 1) s ^= x[k]; x[col] = s; }
        nsb[i] = x; }
    /* evaluate OR-constraints at random points of the solution space */
    uint8_t *x = malloc(NV);
    for (int trial = 0; trial < 5; trial++) {
        memcpy(x, x0, NV); if (trial) for (int i = 0; i < nfree; i++) if (rnd() & 1) for (int k = 0; k < NV; k++) x[k] ^= nsb[i][k];
        long viol = 0;
        for (long o = 0; o < nor; o++) { int first = -1, okc = 0;
            for (int k = oroff[o]; k < oroff[o + 1]; k++) { int val = orc[k].nb; for (int t = 0; t < orc[k].nv; t++) val ^= x[orc[k].v[t]]; if (first < 0) first = val; else if (val != first) okc = 1; }
            if (!okc) viol++; }
        long eqbad = 0; for (long e = 0; e < neq; e++) { int val = eqrhs[e]; for (int k = eqoff[e]; k < eqoff[e + 1]; k++) val ^= x[eqv[k]]; if (val) eqbad++; }
        printf("random solution %d: violated OR-constraints %ld of %ld (equations violated %ld)\n", trial, viol, nor, eqbad); fflush(stdout);
    }
    if (argc > 2) {
        char fn[512]; sprintf(fn, "%s.sol", argv[2]); FILE *g = fopen(fn, "w"); fprintf(g, "%d %d\n", NV, nfree);
        for (int k = 0; k < NV; k++) fputc('0' + x0[k], g); fputc('\n', g);
        for (int i = 0; i < nfree; i++) { for (int k = 0; k < NV; k++) fputc('0' + nsb[i][k], g); fputc('\n', g); } fclose(g);
        sprintf(fn, "%s.or", argv[2]); g = fopen(fn, "wb"); fwrite(&nor, 8, 1, g); fwrite(oroff, 4, nor + 1, g); fwrite(orc, sizeof(cls_t), norc, g); fclose(g);
        sprintf(fn, "%s.eq", argv[2]); g = fopen(fn, "wb"); fwrite(&neq, 8, 1, g); fwrite(eqoff, 4, neq + 1, g); fwrite(eqv, 4, eqoff[neq], g); fwrite(eqrhs, 1, neq, g); fclose(g);
        printf("wrote %s.sol, %s.or and %s.eq\n", argv[2], argv[2], argv[2]);
    }
    return 0;
}
