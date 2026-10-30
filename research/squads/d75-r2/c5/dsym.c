/* dsym.c (card c5, squad d75-r2): doubly symmetric Haar connection sets.
 * Haar graph H(G,S), valency 7, (g,A) ~ (s g,B).  X = S^-1 S.  Diameter 5 iff XX = G (A-A within 4), YY = G (B-B),
 * YYS = G (A-B), Y = S S^-1.  Here S is self-dual: psi(S) = S for psi(x) = beta(x)^-1 (beta an involutory
 * automorphism or the identity), so beta(X) = Y and XX = G already gives YY = G; only XX = G is tested
 * (fullcheck re-verifies YY and YYS for every set that passes, as a sanity check).
 * Also alpha(S) = S for an automorphism alpha of order 2 or 3 commuting with beta.
 * For each beta (identity, or an involution class rep from the ALPHA 2 lines of the .ht file) and alpha
 * (for beta = identity: the ALPHA 2/3 class reps; for beta = class rep: every automorphism of order 2/3 in the
 * centralizer of beta, from AUTS), K = <alpha, psi> acts on G as a permutation group (alpha and psi commute).
 * S = {e} + union of K-orbits (e is K-fixed), |S| = 7.  Enumerates all such S.
 * usage: dsym FILE.ht AUTS.txt      env: EDGDIR=dir (edge lists of the first hits), MAXSETS=n per pair, ONLY=i (beta index)
 * AUTS.txt: first line = number of automorphisms, then one perm per line (images of 0..n-1), from allaut.g.
 * Output: PAIR lines (one per (alpha,beta)), SOL lines (hits), and a DONE line.
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

static int n;
static uint16_t *mul; static int *inv;
#define M(a,b) mul[(size_t)(a) * n + (b)]

static int nalp = 0; static int alp_p[128]; static uint16_t *alp_perm[128];
static int na = 0; static uint16_t **A;

static int rdint(FILE *f) { int x; if (fscanf(f, "%d", &x) != 1) { fprintf(stderr, "read error\n"); exit(1); } return x; }

static void load_ht(const char *path) {
    FILE *f = fopen(path, "r"); if (!f) { perror(path); exit(1); }
    n = rdint(f); (void)rdint(f);
    mul = malloc(sizeof(uint16_t) * (size_t)n * n); inv = malloc(sizeof(int) * n);
    for (size_t i = 0; i < (size_t)n * n; i++) mul[i] = rdint(f);
    for (int i = 0; i < n; i++) inv[i] = rdint(f);
    char w[32];
    while (fscanf(f, "%31s", w) == 1) {
        if (!strcmp(w, "ALPHA")) {
            int p = rdint(f); uint16_t *pm = malloc(sizeof(uint16_t) * n);
            for (int i = 0; i < n; i++) pm[i] = rdint(f);
            if (fscanf(f, "%31s", w) != 1 || strcmp(w, "CENT")) { fprintf(stderr, "format\n"); exit(1); }
            int k = rdint(f); for (int j = 0; j < k * n; j++) (void)rdint(f);   /* skip centralizer generators */
            alp_p[nalp] = p; alp_perm[nalp] = pm; nalp++;
        } else if (!strcmp(w, "INV") || !strcmp(w, "IDX2")) { fprintf(stderr, "unexpected line %s\n", w); exit(1); }
    }
    fclose(f);
    for (int i = 0; i < n; i++) if (M(0, i) != i || M(i, 0) != i || M(i, inv[i]) != 0) { fprintf(stderr, "bad table\n"); exit(1); }
}
static void load_auts(const char *path) {
    FILE *f = fopen(path, "r"); if (!f) { perror(path); exit(1); }
    na = rdint(f); A = malloc(sizeof(uint16_t *) * na);
    for (int a = 0; a < na; a++) { A[a] = malloc(sizeof(uint16_t) * n); for (int i = 0; i < n; i++) A[a][i] = rdint(f); }
    fclose(f);
}

/* ---- orbit machinery ---- */
static int *ua;
static int uf_find(int x) { while (ua[x] != x) { ua[x] = ua[ua[x]]; x = ua[x]; } return x; }
static void uf_union(int a, int b) { a = uf_find(a); b = uf_find(b); if (a != b) ua[a] = b; }
static int m_orb, *ost, *osz, *oel; static int Sb[16]; static long long nsets, nxx, nfull, nhits, pair_hits;
static long long cap_sets; static int capped; static long long cost_stride = 16;
static uint32_t *mk, stM = 0; static int *ord;

static int pp_xx(const int *S, int k) {   /* X = S^-1 S: is every z in X X ? */
    int X[64], nx = 0; stM++;
    for (int i = 0; i < k; i++) for (int j = 0; j < k; j++) {
        int x = M(inv[S[i]], S[j]);
        if (mk[x] != stM) { mk[x] = stM; X[nx++] = x; }
    }
    const uint16_t *rows[64]; for (int i = 0; i < nx; i++) rows[i] = mul + (size_t)inv[X[i]] * n;
    for (int t = 0; t < n; t++) { int z = ord[t], ok = 0;
        for (int i = 0; i < nx; i++) if (mk[rows[i][z]] == stM) { ok = 1; break; }
        if (!ok) { if (t) { int u = t / 2; ord[t] = ord[u]; ord[u] = z; } return 0; } }
    return 1;
}
static int fullcheck(const int *S, int k) {   /* YY = G and YY S = G */
    int Y[64], ny = 0; char *seen = calloc(n, 1);
    for (int i = 0; i < k; i++) for (int j = 0; j < k; j++) { int y = M(S[i], inv[S[j]]); if (!seen[y]) { seen[y] = 1; Y[ny++] = y; } }
    char *yy = calloc(n, 1), *odd = calloc(n, 1);
    for (int i = 0; i < ny; i++) for (int j = 0; j < ny; j++) yy[M(Y[i], Y[j])] = 1;
    int cy = 0; for (int z = 0; z < n; z++) cy += yy[z];
    for (int z = 0; z < n; z++) if (yy[z]) for (int i = 0; i < k; i++) odd[M(z, S[i])] = 1;
    int ok = (cy == n); for (int z = 0; z < n; z++) if (!odd[z]) ok = 0;
    free(seen); free(yy); free(odd); return ok;
}

static int edg_written = 0; static const char *edgdir = NULL;
static void hit(const int *S, int k, int ai, int bi) {
    nhits++; pair_hits++;
    printf("SOL alpha %d beta %d S", ai, bi); for (int i = 0; i < k; i++) printf(" %d", S[i]); printf("\n"); fflush(stdout);
    if (edgdir && edg_written < 20) {
        char path[1024]; snprintf(path, sizeof path, "%s/hit_%d.edges", edgdir, edg_written);
        FILE *f = fopen(path, "w"); if (f) { fprintf(f, "%d\n", 2 * n);
            for (int g = 0; g < n; g++) for (int i = 0; i < k; i++) fprintf(f, "%d %d\n", g, n + M(S[i], g));
            fclose(f); }
        edg_written++;
    }
}

static int want_sum = 6;
static int *stA; static uint32_t stC = 0; static int best_cost = 1 << 30; static int best_S[8]; static int best_ai, best_bi;
static int xx_cost(const int *S, int k) {   /* exact |G \ XX| */
    int X[64], nx = 0; stC++; if (!stA) stA = calloc(n, sizeof(int));
    static uint32_t *mx = NULL; if (!mx) mx = calloc(n, sizeof(uint32_t));
    static uint32_t stX = 0; stX++;
    for (int i = 0; i < k; i++) for (int j = 0; j < k; j++) { int x = M(inv[S[i]], S[j]); if (mx[x] != stX) { mx[x] = stX; X[nx++] = x; } }
    int cov = 0;
    for (int i = 0; i < nx; i++) for (int j = 0; j < nx; j++) { int z = M(X[i], X[j]); if (stA[z] != (int)stC) { stA[z] = (int)stC; cov++; } }
    return n - cov;
}
static void test_set(int ai, int bi) {
    nsets++;
    if (nsets % cost_stride == 0) { int c = xx_cost(Sb, 7); if (c < best_cost) { best_cost = c; memcpy(best_S, Sb, sizeof best_S); best_ai = ai; best_bi = bi; } }
    if (!pp_xx(Sb, 7)) return;
    nxx++;
    if (!fullcheck(Sb, 7)) { nfull++; return; }
    hit(Sb, 7, ai, bi);
}
static void rec(int start, int sum, int k, int ai, int bi) {   /* Sb[0..k-1] filled, sum = total size of chosen orbits */
    if (capped) return;
    if (sum == want_sum) { if (nsets >= cap_sets) { capped = 1; return; } test_set(ai, bi); return; }
    for (int o = start; o < m_orb; o++) {
        if (sum + osz[o] > want_sum) continue;
        for (int j = 0; j < osz[o]; j++) Sb[k + j] = oel[ost[o] + j];
        rec(o + 1, sum + osz[o], k + osz[o], ai, bi);
        if (capped) return;
    }
}

static int is_id(const uint16_t *p) { for (int i = 0; i < n; i++) if (p[i] != i) return 0; return 1; }
static int order_23(const uint16_t *p) {   /* 2 or 3 if exactly, else 0 */
    if (is_id(p)) return 0;
    uint16_t *q = malloc(sizeof(uint16_t) * n); for (int i = 0; i < n; i++) q[i] = p[p[i]];
    if (is_id(q)) { free(q); return 2; }
    for (int i = 0; i < n; i++) q[i] = p[q[i]];
    int r = is_id(q); free(q); return r ? 3 : 0;
}
static int commute(const uint16_t *a, const uint16_t *b) { for (int i = 0; i < n; i++) if (a[b[i]] != b[a[i]]) return 0; return 1; }

/* one pair (alpha, beta): K = <alpha, psi>, psi(x) = inv[beta(x)] */
static void run_pair(const uint16_t *al, int ord_al, const uint16_t *be, int ai, int bi, const char *tag) {
    int *psi = malloc(sizeof(int) * n);
    for (int x = 0; x < n; x++) psi[x] = inv[be[x]];
    ua = malloc(sizeof(int) * n); for (int x = 0; x < n; x++) ua[x] = x;
    for (int x = 0; x < n; x++) { uf_union(x, al[x]); uf_union(x, psi[x]); }
    int *root = malloc(sizeof(int) * n), *oid = malloc(sizeof(int) * n);
    for (int x = 0; x < n; x++) oid[x] = -1;
    int no = 0; int hist[8] = {0};
    int *cnt = calloc(n + 1, sizeof(int));
    for (int x = 0; x < n; x++) { root[x] = uf_find(x); cnt[root[x]]++; }
    for (int x = 0; x < n; x++) if (cnt[x]) no++;
    m_orb = 0; ost = malloc(sizeof(int) * no); osz = malloc(sizeof(int) * no); oel = malloc(sizeof(int) * n);
    int *ostart = malloc(sizeof(int) * (n + 1)); int ne = 0;
    /* orbit of element 0 must be {0} */
    int zero_root = root[0]; if (cnt[zero_root] != 1) { fprintf(stderr, "orbit of e not trivial\n"); exit(1); }
    /* group elements by root */
    int *fill = calloc(n + 1, sizeof(int)); int *start_of = malloc(sizeof(int) * (n + 1));
    int acc = 0; for (int r = 0; r < n; r++) { start_of[r] = acc; acc += cnt[r]; }
    for (int x = 0; x < n; x++) { int r = root[x]; oel[start_of[r] + fill[r]++] = x; }
    for (int r = 0; r < n; r++) if (cnt[r] && r != zero_root) {
        ost[m_orb] = start_of[r]; osz[m_orb] = cnt[r]; m_orb++;
        if (cnt[r] <= 6) hist[cnt[r]]++;
    }
    (void)ostart; (void)oid; (void)ne;
    int fixed_nonid = 0; for (int o = 0; o < m_orb; o++) if (osz[o] == 1) fixed_nonid++;
    /* run the enumeration; orbits with size > 6 are never used */
    long long s0 = nsets, x0 = nxx; pair_hits = 0; capped = 0;
    Sb[0] = 0;
    rec(0, 0, 1, ai, bi);
    printf("PAIR %s alpha %d ord %d beta %d orbits %d (size1 %d size2 %d size3 %d size4 %d size6 %d) sets %lld xxpass %lld hits %lld%s\n",
           tag, ai, ord_al, bi, m_orb, hist[1], hist[2], hist[3], hist[4], hist[6], nsets - s0, nxx - x0, pair_hits, capped ? " CAPPED" : "");
    fflush(stdout);
    (void)fixed_nonid;
    free(psi); free(ua); free(root); free(oid); free(cnt); free(ost); free(osz); free(oel); free(ostart); free(fill); free(start_of);
}

int main(int argc, char **argv) {
    if (argc < 3) { fprintf(stderr, "usage: dsym FILE.ht AUTS.txt\n"); return 2; }
    load_ht(argv[1]); load_auts(argv[2]);
    edgdir = getenv("EDGDIR");
    cap_sets = getenv("MAXSETS") ? atoll(getenv("MAXSETS")) : 300000000LL;
    int only = getenv("ONLY") ? atoi(getenv("ONLY")) : -1;
    if (getenv("COSTSTRIDE")) cost_stride = atoll(getenv("COSTSTRIDE"));
    mk = calloc(n, sizeof(uint32_t)); ord = malloc(sizeof(int) * n); for (int i = 0; i < n; i++) ord[i] = i;
    printf("GROUP %s n %d auts %d alpha-lines %d\n", argv[1], n, na, nalp);
    /* betas: identity (index 0) then the ALPHA 2 class reps */
    uint16_t *idp = malloc(sizeof(uint16_t) * n); for (int i = 0; i < n; i++) idp[i] = i;
    int nb = 1; uint16_t *bperm[128]; bperm[0] = idp;
    for (int j = 0; j < nalp; j++) if (alp_p[j] == 2) { bperm[nb] = alp_perm[j]; nb++; }
    for (int bi = 0; bi < nb; bi++) {
        if (only >= 0 && bi != only) continue;
        const uint16_t *be = bperm[bi];
        if (bi > 0 && order_23(be) != 2) { printf("beta %d not an involution\n", bi); continue; }
        if (bi == 0) {
            /* alpha: ALPHA 2/3 class reps (complete up to conjugacy, beta = identity is central) */
            for (int j = 0; j < nalp; j++) if (alp_p[j] == 2 || alp_p[j] == 3) {
                if (alp_p[j] == 2 || alp_p[j] == 3) {
                    int o = order_23(alp_perm[j]); if (!o) { printf("bad alpha\n"); continue; }
                    /* skip alpha == psi (cannot happen for non-abelian G); skip nothing else */
                    run_pair(alp_perm[j], o, be, 1000 + j, bi, "b0");
                }
            }
        } else {
            for (int a = 0; a < na; a++) {
                int o = order_23(A[a]); if (!o) continue;
                if (!commute(A[a], be)) continue;
                run_pair(A[a], o, be, a, bi, "bk");
            }
        }
    }
    printf("BESTCOST %d (sampled 1/16 of sets) alpha %d beta %d S", best_cost, best_ai, best_bi);
    for (int i = 0; i < 7; i++) printf(" %d", best_S[i]);
    printf("\n");
    printf("DONE sets %lld xxpass %lld fullfail %lld hits %lld\n", nsets, nxx, nfull, nhits);
    return 0;
}
