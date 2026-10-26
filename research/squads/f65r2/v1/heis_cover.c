/*
 * Independent check (card v1, round f65r2).
 * Claim: min over 6-subsets S of G of |G \ (S^-1 S)^2|, G = Heis(p) (default p=7).
 *
 * Group: elements (a,b,c) mod p, product (a,b,c)(a',b',c') = (a+a', b+b', c+c'+a*b').
 * Index = a*p*p + b*p + c.
 *
 * Modes:
 *   heis P full   : exhaustive over all 6-subsets S containing e (small p only, e.g. p=3)
 *   heis P reduced: WLOG e in S, (1,0,0) in S (Aut transitive on noncentral), and
 *                   one further element r taken as a representative of the orbits of
 *                   Stab_Aut((1,0,0)) on G\{e,s1}; the other 3 elements are free.
 *   cyc N full    : exhaustive over 6-subsets containing 0 of cyclic group Z_N (test)
 *
 * Automorphisms of Heis(p) (p odd) are generated explicitly as
 *   phi(a,b,c) = (M(a,b), det(M)*(c + al*a + be*b) + Q(a,b)),  M in GL(2,p),
 *   Q(u) = D(u,u)/2, D(u,v) = omega(Mu,Mv) - det(M)*omega(u,v), omega(u,v)=u1*v2.
 * Every candidate is verified to be an automorphism (generator test: phi(s*g)=phi(s)phi(g)
 * for generators s=x,y and all g, plus bijectivity), and the count must equal p^2*|GL(2,p)|.
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

#define MAXN 400
#define MAXQ 64
#define MAXW 7

static int N;             /* group order */
static int *MUL;          /* MUL[x*N+y] */
static int *INV;          /* INV[x] */
static int P;             /* prime for Heis, or 0 for cyclic */
static int NCYC;          /* cyclic order when P==0 */

static int md(int x, int m) { x %= m; if (x < 0) x += m; return x; }

static int enc_h(int a, int b, int c) { return md(a, P) * P * P + md(b, P) * P + md(c, P); }
static void dec_h(int x, int *a, int *b, int *c) { *a = x / (P * P); *b = (x / P) % P; *c = x % P; }

static void build_group(void) {
    int i, j;
    if (P == 0) {
        N = NCYC;
        MUL = malloc(sizeof(int) * N * N);
        INV = malloc(sizeof(int) * N);
        for (i = 0; i < N; i++) for (j = 0; j < N; j++) MUL[i * N + j] = (i + j) % N;
        for (i = 0; i < N; i++) INV[i] = (N - i) % N;
        return;
    }
    N = P * P * P;
    MUL = malloc(sizeof(int) * N * N);
    INV = malloc(sizeof(int) * N);
    for (i = 0; i < N; i++) {
        int a, b, c;
        dec_h(i, &a, &b, &c);
        for (j = 0; j < N; j++) {
            int a2, b2, c2;
            dec_h(j, &a2, &b2, &c2);
            MUL[i * N + j] = enc_h(a + a2, b + b2, c + c2 + a * b2);
        }
    }
    for (i = 0; i < N; i++) {
        INV[i] = -1;
        for (j = 0; j < N; j++) if (MUL[i * N + j] == 0) { INV[i] = j; break; }
        if (INV[i] < 0) { fprintf(stderr, "no inverse\n"); exit(1); }
    }
}

/* ---------- covering computation ---------- */
static int covered_count_uncovered(const int *S, int k) {
    static int inQ[MAXN];
    int Q[MAXQ], nq = 0, i, j, a, b;
    uint64_t bits[MAXW];
    int cnt = 0;
    for (i = 0; i < k; i++)
        for (j = 0; j < k; j++) {
            int q = MUL[INV[S[i]] * N + S[j]];
            if (!inQ[q]) { inQ[q] = 1; Q[nq++] = q; }
        }
    for (i = 0; i < nq; i++) inQ[Q[i]] = 0;
    memset(bits, 0, sizeof(bits));
    for (a = 0; a < nq; a++) {
        const int *row = &MUL[Q[a] * N];
        for (b = 0; b < nq; b++) {
            int t = row[Q[b]];
            bits[t >> 6] |= 1ULL << (t & 63);
        }
    }
    for (i = 0; i < (N + 63) / 64; i++) cnt += __builtin_popcountll(bits[i]);
    return N - cnt;
}

/* ---------- automorphisms (Heis only) ---------- */
static int *AUT = NULL;   /* naut * N */
static int naut = 0;

static int is_automorphism(const int *phi) {
    int s, g, seen_ok = 1;
    static int seen[MAXN];
    int gens[2];
    gens[0] = enc_h(1, 0, 0);
    gens[1] = enc_h(0, 1, 0);
    if (phi[0] != 0) return 0;
    memset(seen, 0, sizeof(int) * N);
    for (g = 0; g < N; g++) {
        if (seen[phi[g]]) return 0;
        seen[phi[g]] = 1;
    }
    for (s = 0; s < 2; s++)
        for (g = 0; g < N; g++)
            if (phi[MUL[gens[s] * N + g]] != MUL[phi[gens[s]] * N + phi[g]]) { seen_ok = 0; break; }
    return seen_ok;
}

static void build_automorphisms(void) {
    int cap = P * P * (P * P * P * P), m11, m12, m21, m22, al, be, cnt = 0;
    AUT = malloc(sizeof(int) * (size_t)cap * N);
    int inv2 = 0;
    for (int t = 1; t < P; t++) if ((2 * t) % P == 1) inv2 = t;
    int *phi = malloc(sizeof(int) * N);
    int bad = 0, total_gl = 0;
    for (m11 = 0; m11 < P; m11++) for (m12 = 0; m12 < P; m12++)
    for (m21 = 0; m21 < P; m21++) for (m22 = 0; m22 < P; m22++) {
        int det = md(m11 * m22 - m12 * m21, P);
        if (det == 0) continue;
        total_gl++;
        for (al = 0; al < P; al++) for (be = 0; be < P; be++) {
            int x;
            for (x = 0; x < N; x++) {
                int a, b, c;
                dec_h(x, &a, &b, &c);
                int a1 = md(m11 * a + m12 * b, P), b1 = md(m21 * a + m22 * b, P);
                /* D(u,u) = (Mu)_1 (Mu)_2 - det * a*b ; Q(u) = D(u,u)/2 */
                int Du = md(a1 * b1 - det * a * b, P);
                int Qu = md(Du * inv2, P);
                int c1 = md(det * (c + al * a + be * b) + Qu, P);
                phi[x] = enc_h(a1, b1, c1);
            }
            if (is_automorphism(phi)) {
                memcpy(&AUT[(size_t)cnt * N], phi, sizeof(int) * N);
                cnt++;
            } else bad++;
        }
    }
    naut = cnt;
    printf("GL(2,%d) order %d; candidate maps %d; verified automorphisms %d; rejected %d\n",
           P, total_gl, total_gl * P * P, naut, bad);
    free(phi);
}

/* ---------- enumeration ---------- */
static long long nsets = 0;
static int best_min = 1 << 30;
static long long best_count = 0;
static int best_set[8];
static int best_k = 0;

static void record(const int *S, int k) {
    int u = covered_count_uncovered(S, k);
    nsets++;
    if (u < best_min) {
        best_min = u; best_count = 0;
        memcpy(best_set, S, sizeof(int) * k); best_k = k;
    }
    if (u == best_min) best_count++;
}

static void print_elem(int x) {
    if (P == 0) { printf("%d", x); return; }
    int a, b, c; dec_h(x, &a, &b, &c);
    printf("(%d,%d,%d)", a, b, c);
}

/* full enumeration over k-subsets of G\{0} together with 0 */
static void full_enum(int k) {
    int idx[8], S[8], i;
    int r = k - 1;      /* choose r elements from 1..N-1 */
    for (i = 0; i < r; i++) idx[i] = i + 1;
    while (1) {
        S[0] = 0;
        for (i = 0; i < r; i++) S[i + 1] = idx[i];
        record(S, k);
        /* next combination */
        int j = r - 1;
        while (j >= 0 && idx[j] == N - r + j) j--;
        if (j < 0) break;
        idx[j]++;
        for (i = j + 1; i < r; i++) idx[i] = idx[i - 1] + 1;
    }
}

int main(int argc, char **argv) {
    const char *mode = "reduced";
    if (argc < 3) {
        fprintf(stderr, "usage: %s heis P [full|reduced] | cyc N [full]\n", argv[0]);
        return 1;
    }
    struct timespec t0, t1;
    clock_gettime(CLOCK_MONOTONIC, &t0);
    if (strcmp(argv[1], "heis") == 0) {
        P = atoi(argv[2]);
        if (argc > 3) mode = argv[3];
    } else if (strcmp(argv[1], "cyc") == 0) {
        P = 0; NCYC = atoi(argv[2]);
        mode = "full";
    } else { fprintf(stderr, "bad group\n"); return 1; }

    build_group();
    const int K = (argc > 4) ? atoi(argv[4]) : 6;
    if (P == 0 || strcmp(mode, "full") == 0) {
        full_enum(K);
    } else {
        build_automorphisms();
        int s1 = enc_h(1, 0, 0), e = 0, s1_count = 0;
        /* check transitivity on noncentral and central elements */
        {
            static int seen[MAXN];
            int orbit_nc = 0, orbit_c = 0, x;
            memset(seen, 0, sizeof(seen));
            for (x = 0; x < N; x++) {
                if (seen[x]) continue;
                /* orbit of x under all automorphisms */
                int ox = 0;
                static int mark[MAXN];
                memset(mark, 0, sizeof(mark));
                for (int t = 0; t < naut; t++) {
                    int y = AUT[(size_t)t * N + x];
                    if (!mark[y]) { mark[y] = 1; ox++; }
                }
                for (int y = 0; y < N; y++) if (mark[y]) seen[y] = 1;
                int a, b, c; dec_h(x, &a, &b, &c);
                if (a || b) { orbit_nc = ox; }
                else if (c) { orbit_c = ox; }
            }
            printf("orbit of (1,0,0) noncentral? checking: orbit size of noncentral element = %d (expect 336)\n", orbit_nc);
            printf("orbit size of central nonidentity element (0,0,1) = %d (expect 6)\n", orbit_c);
        }
        /* stabiliser of s1 */
        int *H = malloc(sizeof(int) * naut);
        int nh = 0;
        for (int t = 0; t < naut; t++) if (AUT[(size_t)t * N + s1] == s1) H[nh++] = t;
        printf("|Stab(s1)| = %d (expect %d)\n", nh, naut / 336);
        /* orbits of H on G \ {e, s1} */
        int *rep = malloc(sizeof(int) * N), nrep = 0;
        static int assigned[MAXN];
        memset(assigned, 0, sizeof(assigned));
        assigned[e] = 1; assigned[s1] = 1;
        for (int x = 0; x < N; x++) {
            if (assigned[x]) continue;
            rep[nrep++] = x;
            for (int t = 0; t < nh; t++) assigned[AUT[(size_t)H[t] * N + x]] = 1;
        }
        printf("H-orbit representatives on G\\{e,s1}: %d\n", nrep);
        for (int ri = 0; ri < nrep; ri++) {
            int r = rep[ri];
            int L[MAXN], nl = 0;
            for (int x = 0; x < N; x++) if (x != e && x != s1 && x != r) L[nl++] = x;
            long long before = nsets;
            int bmin_before = best_min;
            {
                int m = K - 3, idx[8], S[8], i2;
                if (m == 0) { int S0[8] = { e, s1, r }; record(S0, 3); }
                else {
                    for (i2 = 0; i2 < m; i2++) idx[i2] = i2;
                    while (1) {
                        S[0] = e; S[1] = s1; S[2] = r;
                        for (i2 = 0; i2 < m; i2++) S[3 + i2] = L[idx[i2]];
                        record(S, K);
                        int j2 = m - 1;
                        while (j2 >= 0 && idx[j2] == nl - m + j2) j2--;
                        if (j2 < 0) break;
                        idx[j2]++;
                        for (i2 = j2 + 1; i2 < m; i2++) idx[i2] = idx[i2 - 1] + 1;
                    }
                }
            }
            printf("rep %d = ", ri); print_elem(r);
            printf(": sets %lld, running min %d\n", nsets - before, best_min);
            (void)bmin_before;
        }
        (void)s1_count;
        free(H); free(rep);
    }
    clock_gettime(CLOCK_MONOTONIC, &t1);
    double secs = (t1.tv_sec - t0.tv_sec) + 1e-9 * (t1.tv_nsec - t0.tv_nsec);

    printf("group: %s order %d, mode %s\n", P == 0 ? "cyclic" : "Heis(p)", N, mode);
    printf("sets checked: %lld\n", nsets);
    printf("minimum uncovered |G \\ (S^-1S)^2|: %d\n", best_min);
    printf("sets attaining minimum (among those checked): %lld\n", best_count);
    printf("a minimiser S = {");
    for (int i = 0; i < best_k; i++) { if (i) printf(", "); print_elem(best_set[i]); }
    printf("}\n");
    printf("covers everything: %s\n", best_min == 0 ? "YES" : "no");
    printf("time: %.2f s\n", secs);
    return 0;
}
