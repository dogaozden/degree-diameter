/* ---------------- ZOPT mode (cell-10-8 session): exhaustive Z_n offsets for fixed Q-parts ----------------
 * G = Q x Z_n with n prime, ORBIT mode with f = 1 (S[0] = e) and m <= 4 orbits, alpha acting on Z_n by z -> AR z.
 * Letter i of orbit j is alpha^i(x_j), whose Z-part is AR^i z_j. A word's Z-part is therefore sum_j c_j(word) z_j with
 * c_j in Z_n determined by the letters alone, while its Q-part does not depend on z at all. So, for the Q-parts of a
 * given S, the cost of every offset vector z = (z_1..z_m) can be computed from the fibres
 *   C_q = { c(w) : w a binding word (odd length <= D-1, from side A) with Q-part q }:
 * the fibre over q is complete iff { c.z : c in C_q } = Z_n. Scaling z by a unit gives an isomorphic graph
 * ((q, t) -> (q, lambda t) is an automorphism of G), so only projective points of PG(m-1, n) are tried.
 * ZOPT=1: Q-parts from S (use with CKPT=file to start from a run's best set). ZOPT=r:K: K random symmetric S.
 * Prints the cost of the given z, the best z, its cost and how many z have cost 0; a cost-0 set is checked by the
 * full diameter check and written to the output file. */
static int zcmpi(const void *a, const void *b) { int x = *(const int *)a, y = *(const int *)b; return (x > y) - (x < y); }
static int Zn, Zm, Zk, *Zorb, *Zco, **ZLT, **ZLI, *Zq; static int *Zc; static long long Znrec;
static void zdfs(int depth, int q, int c0, int c1, int c2, int c3, int last) {
    if (depth & 1) { Zq[Znrec] = q; Zc[Znrec] = ((c0 * Zn + c1) * Zn + c2) * Zn + c3; Znrec++; }
    if (depth == D - 1) return;
    for (int u = 0; u < d; u++) {
        if (u == last) continue;
        int nqv, j = Zorb[u], s = Zco[u], cc[4] = {c0, c1, c2, c3};
        if (depth % 2 == 0) { nqv = ZLT[u][q]; if (j >= 0) cc[j] = (cc[j] + s) % Zn; }       /* side A -> B: s_u g */
        else { nqv = ZLI[u][q]; if (j >= 0) cc[j] = (cc[j] - s + Zn) % Zn; }                   /* side B -> A: s_u^-1 g */
        zdfs(depth + 1, nqv, cc[0], cc[1], cc[2], cc[3], u);
    }
}
static int zopt_main(ctx *c0, const char *out) {
    Zn = ncyc; Zm = OM; Zk = OK_; int nq = Q->order;
    if (OF != 1 || Zm > 4 || Zn < 3 || S[0] != ident) { fprintf(stderr, "ZOPT needs f = 1 (S[0] = e) and m <= 4\n"); return 2; }
    for (int p = 2; p * p <= Zn; p++) if (Zn % p == 0) { fprintf(stderr, "ZOPT needs n prime\n"); return 2; }
    int rp[MAXD]; rp[0] = 1; for (int i = 1; i < Zk; i++) rp[i] = (int)((long long)rp[i - 1] * AR % Zn);
    Zorb = malloc(sizeof(int) * d); Zco = malloc(sizeof(int) * d); ZLT = malloc(sizeof(int *) * d); ZLI = malloc(sizeof(int *) * d);
    for (int u = 0; u < d; u++) { ZLT[u] = malloc(sizeof(int) * nq); ZLI[u] = malloc(sizeof(int) * nq); }
    Zorb[0] = -1; Zco[0] = 0;
    for (int j = 0; j < Zm; j++) for (int i = 0; i < Zk; i++) { Zorb[ostart(j) + i] = j; Zco[ostart(j) + i] = rp[i]; }
    long long W = (long long)Wwords(d, D) + 16;
    Zq = malloc(sizeof(int) * W); Zc = malloc(sizeof(int) * W);
    int *off = malloc(sizeof(int) * (nq + 1)), *ord = malloc(sizeof(int) * nq), *cnt = malloc(sizeof(int) * (nq + 1));
    int *F = malloc(sizeof(int) * W); uint8_t *F0 = malloc(W), *F1 = malloc(W), *F2 = malloc(W), *F3 = malloc(W);
    int *MODT = malloc(sizeof(int) * 4 * Zn * Zn); for (int t = 0; t < 4 * Zn * Zn; t++) MODT[t] = t % Zn;
    const char *zs = getenv("ZOPT"); int nrand = 0; if (zs[0] == 'r') nrand = atoi(zs + 2);
    int reps = nrand ? nrand : 1; long long nzero_tot = 0; long long hist[64] = {0};
    for (int rep = 0; rep < reps; rep++) {
        if (nrand) { for (int j = 0; j < Zm; j++) for (int i = 0; i < Zk; i++) S[ostart(j) + i] = -1 - ostart(j) - i;
                     for (int j = 0; j < Zm; j++) { int o[MAXD]; random_orbit(j, o); for (int i = 0; i < Zk; i++) S[ostart(j) + i] = o[i]; } }
        int zj[4] = {0, 0, 0, 0};
        for (int j = 0; j < Zm; j++) { zj[j] = S[ostart(j)] % Zn;
            for (int i = 0; i < Zk; i++) { int u = ostart(j) + i;
                if (S[u] % Zn != (int)((long long)rp[i] * zj[j] % Zn)) { fprintf(stderr, "ZOPT: orbit %d letter %d: z-part mismatch\n", j, i); return 2; } } }
        for (int u = 0; u < d; u++) { int a = S[u] / Zn, ai = qinv(Q, a); for (int x = 0; x < nq; x++) { ZLT[u][x] = qmul(Q, a, x); ZLI[u][x] = qmul(Q, ai, x); } }
        Znrec = 0; zdfs(0, Q->ident, 0, 0, 0, 0, -1);
        /* counting sort by Q-part, dedup per fibre */
        memset(cnt, 0, sizeof(int) * (nq + 1));
        for (long long t = 0; t < Znrec; t++) cnt[Zq[t] + 1]++;
        for (int x = 0; x < nq; x++) cnt[x + 1] += cnt[x];
        memcpy(off, cnt, sizeof(int) * (nq + 1));
        for (long long t = 0; t < Znrec; t++) F[cnt[Zq[t]]++] = Zc[t];
        long long tot = 0, dup = 0; int empty = 0;
        for (int x = 0; x < nq; x++) { int a = off[x], b = off[x + 1]; qsort(F + a, b - a, sizeof(int), zcmpi);
            int w = a; for (int t = a; t < b; t++) if (t == a || F[t] != F[t - 1]) F[w++] = F[t];
            dup += (b - a) - (w - a); off[x] = (int)tot;   /* compact in place: write position tot */
            for (int t = a; t < w; t++) { int v = F[t]; F[tot] = v; tot++; }
            cnt[x] = w - a; if (w == a) empty++; }
        off[nq] = (int)tot;
        for (long long t = 0; t < tot; t++) { int v = F[t]; F3[t] = v % Zn; v /= Zn; F2[t] = v % Zn; v /= Zn; F1[t] = v % Zn; v /= Zn; F0[t] = v; }
        for (int x = 0; x < nq; x++) ord[x] = x;
        /* fibres in increasing size: the likeliest to fail come first (insertion-free: sort by size via qsort on keys) */
        { long long *key = malloc(sizeof(long long) * nq); for (int x = 0; x < nq; x++) key[x] = (long long)cnt[x] * nq + x;
          qsort(key, nq, sizeof(long long), cmpll); for (int x = 0; x < nq; x++) ord[x] = (int)(key[x] % nq); free(key); }
        /* evaluate z */
        int zb[4] = {0}; long long best = -1, cz = -1, nzero = 0, nz = 0;
        int zz[4];
        for (int pass = 0; pass < 2; pass++) {
            /* pass 0: the given z exactly; pass 1: every projective point, abort above the best so far */
            long long npts = 1; for (int j = 1; j < Zm; j++) npts *= Zn;   /* points with first coordinate 1 */
            long long total_pts = 0; for (int lead = 0; lead < Zm; lead++) { long long c = 1; for (int j = lead + 1; j < Zm; j++) c *= Zn; total_pts += c; }
            for (long long pi = 0; pi < (pass ? total_pts : 1); pi++) {
                if (!pass) memcpy(zz, zj, sizeof zz);
                else { long long r = pi; int lead = 0; long long c = npts; while (r >= c) { r -= c; lead++; c /= Zn; }
                       for (int j = 0; j < Zm; j++) zz[j] = 0; zz[lead] = 1;
                       for (int j = Zm - 1; j > lead; j--) { zz[j] = (int)(r % Zn); r /= Zn; } }
                long long bound = (!pass || best < 0) ? (1LL << 60) : best;
                long long cost = 0;
                for (int oi = 0; oi < nq && cost <= bound; oi++) {
                    int x = ord[oi]; uint64_t mk[4] = {0, 0, 0, 0}; int seen = 0;
                    for (int t = off[x]; t < off[x + 1]; t++) {
                        int r = MODT[F0[t] * zz[0] + F1[t] * zz[1] + F2[t] * zz[2] + (Zm > 3 ? F3[t] * zz[3] : 0)];

                        uint64_t bit = 1ULL << (r & 63); if (!(mk[r >> 6] & bit)) { mk[r >> 6] |= bit; if (++seen == Zn) break; }
                    }
                    cost += Zn - seen;
                }
                if (!pass) { cz = cost; continue; }
                nz++;
                if (cost == 0) nzero++;
                if (best < 0 || cost < best) { best = cost; memcpy(zb, zz, sizeof zb); }
            }
        }
        if (nrand) { hist[best < 63 ? best : 63]++; nzero_tot += nzero; }
        fprintf(stderr, "ZOPT rep %d: words %lld, distinct (q,c) %lld, duplicate %lld, empty fibres %d; cost at given z %lld; best over %lld points %lld (z = %d %d %d %d); zero-cost points %lld\n",
                rep, Znrec, tot, dup, empty, cz, nz, best, zb[0], zb[1], zb[2], zb[3], nzero);
        if (best == 0 || (!nrand && getenv("ZWRITE"))) {
            for (int j = 0; j < Zm; j++) for (int i = 0; i < Zk; i++) { int u = ostart(j) + i; S[u] = (S[u] / Zn) * Zn + (int)((long long)rp[i] * zb[j] % Zn); }
            for (int u = 0; u < d; u++) { SI[u] = ginv(S[u]); mktab(S[u], TF[u], TI[u]); }
            double sc; long long cfull = cost_any(c0, TF, TI, &sc, NULL, &NOBOUND, 0);
            fprintf(stderr, "ZOPT: haar_sym cost of the new set %lld\n", cfull);
            if (cfull == 0 && check_and_write(c0, out)) { printf("ZOPT RESULT best=0 wrote %s\n", out); return 0; }
        }
    }
    if (nrand) { printf("ZOPT random Q-configurations %d: best-z cost histogram", nrand); for (int h = 0; h < 64; h++) if (hist[h]) printf(" %d:%lld", h, hist[h]); printf("; zero points %lld\n", nzero_tot); }
    return 1;
}
