/* Exhaustive search for S (|S| = K, e in S) in a finite group with
 *   cond1: (S^-1 S)^2 = G,   cond2: (S S^-1)^2 = G.
 * Reduction used: S -> g S and S -> S g preserve both conditions (cond2 up to conjugation),
 * so WLOG e in S; Aut(G) preserves both conditions. Orbit iteration k fixes one element
 * r_k of the k-th Aut-orbit (orbits sorted by decreasing size) as an element of S, and the other
 * K-2 elements come from orbits with index >= k (valid by orderly argument: map some element of S
 * from the smallest-index orbit present to r_k).
 * Fast coverage uses |D|^2 products; every CHECK_EVERY-th set is also verified by brute force
 * over all 4-tuples x1,x2,x3,x4 in S.
 * usage: search groupfile K outfile [check_every]
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

#define MAXN 512
#define MAXK 12

static int n, e, K;
static int *M;
static int inv_[MAXN];
static uint32_t stamp1[MAXN], stamp2[MAXN];
static uint32_t gen1 = 0, gen2 = 0;
static int S[MAXK];
static long long sets_checked = 0, cond1_count = 0, cond2_count = 0, brute_checks = 0, brute_mismatch = 0;
static int min_unc1 = 1 << 30, min_unc2 = 1 << 30;
static long long check_every = 0;
static FILE *out = NULL;
static int nit;
static int reps[MAXN];
static int poolsz[MAXN];
static int *pools[MAXN];
static int nstab = 0;
static int *stab = NULL;     /* stabiliser of reps[0] in Aut(G), as permutations */
static int use_stab = 1;
static long long skipped_canon = 0;

static int cover_count(const int *L, int len, int *cnt_out) {
    gen2++;
    if (gen2 == 0) { memset(stamp2, 0, sizeof stamp2); gen2 = 1; }
    int cnt = 0;
    for (int i = 0; i < len; i++) {
        const int *row = M + (size_t)L[i] * n;
        for (int j = 0; j < len; j++) {
            int c = row[L[j]];
            if (stamp2[c] != gen2) { stamp2[c] = gen2; cnt++; }
        }
    }
    *cnt_out = cnt;
    return n - cnt;
}

/* brute force over all 4-tuples, independent of the D-list construction */
static void brute(int *unc1, int *unc2) {
    static unsigned char c1[MAXN], c2[MAXN];
    memset(c1, 0, sizeof c1); memset(c2, 0, sizeof c2);
    int u1 = 0, u2 = 0;
    for (int a = 0; a < K; a++) for (int b = 0; b < K; b++) for (int c = 0; c < K; c++) for (int d = 0; d < K; d++) {
        int x1 = S[a], x2 = S[b], x3 = S[c], x4 = S[d];
        int p = M[(size_t)inv_[x1] * n + x2], q = M[(size_t)inv_[x3] * n + x4];
        c1[M[(size_t)p * n + q]] = 1;
        p = M[(size_t)x1 * n + inv_[x2]]; q = M[(size_t)x3 * n + inv_[x4]];
        c2[M[(size_t)p * n + q]] = 1;
    }
    for (int g = 0; g < n; g++) { if (!c1[g]) u1++; if (!c2[g]) u2++; }
    *unc1 = u1; *unc2 = u2;
}

static void evaluate(void) {
    sets_checked++;
    /* D1 = S^-1 S as a list of distinct elements */
    static int L1[MAXN], L2[MAXN];
    int len1 = 0;
    gen1++;
    if (gen1 == 0) { memset(stamp1, 0, sizeof stamp1); gen1 = 1; }
    for (int i = 0; i < K; i++) for (int j = 0; j < K; j++) {
        int q = M[(size_t)inv_[S[i]] * n + S[j]];
        if (stamp1[q] != gen1) { stamp1[q] = gen1; L1[len1++] = q; }
    }
    int cnt1, unc1 = cover_count(L1, len1, &cnt1);
    unc1 = n - cnt1;
    if (unc1 < min_unc1) min_unc1 = unc1;
    int unc2 = -1;
    if (unc1 == 0) {
        cond1_count++;
        /* D2 = S S^-1 */
        int len2 = 0;
        static uint32_t st[MAXN]; static uint32_t g = 0;
        g++;
        if (g == 0) { memset(st, 0, sizeof st); g = 1; }
        for (int i = 0; i < K; i++) for (int j = 0; j < K; j++) {
            int q = M[(size_t)S[i] * n + inv_[S[j]]];
            if (st[q] != g) { st[q] = g; L2[len2++] = q; }
        }
        int cnt2;
        unc2 = n - (cover_count(L2, len2, &cnt2), cnt2);
        if (unc2 < min_unc2) min_unc2 = unc2;
        if (unc2 == 0) cond2_count++;
        if (out) {
            fprintf(out, "unc2=%d S=", unc2);
            for (int i = 0; i < K; i++) fprintf(out, "%d%c", S[i], i + 1 < K ? ',' : '\n');
        }
    }
    if (check_every && sets_checked % check_every == 0) {
        int b1, b2;
        brute(&b1, &b2);
        brute_checks++;
        if (b1 != unc1 || (unc1 == 0 && b2 != unc2)) {
            brute_mismatch++;
            if (brute_mismatch < 10)
                fprintf(stderr, "MISMATCH fast(%d,%d) brute(%d,%d)\n", unc1, unc2, b1, b2);
        }
    }
}

/* for iteration 0: keep T only if its sorted image under each stabiliser element is not lexicographically smaller */
static int canonical_T(void) {
    int T[MAXK];
    int r = K - 2;
    for (int i = 0; i < r; i++) T[i] = S[2 + i];
    for (int s = 0; s < nstab; s++) {
        const int *h = stab + (size_t)s * n;
        int img[MAXK];
        for (int i = 0; i < r; i++) img[i] = h[T[i]];
        for (int i = 1; i < r; i++) { int v = img[i], j = i - 1; while (j >= 0 && img[j] > v) { img[j + 1] = img[j]; j--; } img[j + 1] = v; }
        for (int i = 0; i < r; i++) {
            if (img[i] < T[i]) return 0;
            if (img[i] > T[i]) break;
        }
    }
    return 1;
}

static void choose(int it, int depth, int start) {
    int r = K - 2;
    if (depth == r) {
        if (it == 0 && use_stab && !canonical_T()) { skipped_canon++; return; }
        evaluate();
        return;
    }
    for (int i = start; i < poolsz[it]; i++) {
        S[2 + depth] = pools[it][i];
        choose(it, depth + 1, i + 1);
    }
}

int main(int argc, char **argv) {
    if (argc < 4) { fprintf(stderr, "usage: %s groupfile K outfile [check_every] [use_stab]\n", argv[0]); return 1; }
    FILE *f = fopen(argv[1], "r");
    if (!f) { perror("group"); return 1; }
    K = atoi(argv[2]);
    if (argc >= 5) check_every = atoll(argv[4]);
    if (fscanf(f, "%d", &n) != 1) return 1;
    M = malloc(sizeof(int) * (size_t)n * n);
    for (size_t i = 0; i < (size_t)n * n; i++) if (fscanf(f, "%d", &M[i]) != 1) return 1;
    if (fscanf(f, "%d", &e) != 1) return 1;
    if (fscanf(f, "%d", &nit) != 1) return 1;
    for (int it = 0; it < nit; it++) {
        if (fscanf(f, "%d %d", &reps[it], &poolsz[it]) != 2) return 1;
        pools[it] = malloc(sizeof(int) * (poolsz[it] + 1));
        for (int i = 0; i < poolsz[it]; i++) if (fscanf(f, "%d", &pools[it][i]) != 1) return 1;
    }
    if (fscanf(f, "%d", &nstab) != 1) nstab = 0;
    if (nstab > 0) {
        stab = malloc(sizeof(int) * (size_t)nstab * n);
        for (size_t i = 0; i < (size_t)nstab * n; i++) if (fscanf(f, "%d", &stab[i]) != 1) return 1;
    }
    fclose(f);
    if (argc >= 6) use_stab = atoi(argv[5]);
    /* inverses and a sanity check of the table */
    for (int g = 0; g < n; g++) {
        int found = -1;
        for (int h = 0; h < n; h++) if (M[(size_t)g * n + h] == e) { found = h; break; }
        if (found < 0) { fprintf(stderr, "no inverse for %d\n", g); return 1; }
        inv_[g] = found;
    }
    out = fopen(argv[3], "w");
    if (!out) { perror("out"); return 1; }
    for (int it = 0; it < nit; it++) {
        S[0] = e; S[1] = reps[it];
        long long before = sets_checked;
        choose(it, 0, 0);
        fprintf(stderr, "iteration %d: rep=%d pool=%d sets=%lld\n", it, reps[it], poolsz[it], sets_checked - before);
    }
    fclose(out);
    printf("group order n=%d, K=%d\n", n, K);
    printf("total sets checked (reduced enumeration) = %lld\n", sets_checked);
    printf("min uncovered, cond1 = %d\n", min_unc1);
    printf("sets satisfying cond1 = %lld\n", cond1_count);
    printf("min uncovered, cond2 among cond1 sets = %d\n", cond1_count ? min_unc2 : -1);
    printf("sets satisfying both = %lld\n", cond2_count);
    printf("iteration-0 sets skipped by stabiliser reduction = %lld (stabiliser order %d, use_stab=%d)\n", skipped_canon, nstab, use_stab);
    printf("brute-force cross checks = %lld, mismatches = %lld\n", brute_checks, brute_mismatch);
    return 0;
}
