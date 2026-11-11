static int gcd_i(int a, int b) { while (b) { int t = a % b; a = b; b = t; } return a; }
static int *uf; static int uf_find(int a) { while (uf[a] != a) { uf[a] = uf[uf[a]]; a = uf[a]; } return a; }
static void uf_union(int a, int b) { a = uf_find(a); b = uf_find(b); if (a != b) { if (a < b) uf[b] = a; else uf[a] = b; } }

/* ---- symmetry (both exact) ----
 * meta groups: AUT = verified maps phi(a + m j) = (u a + c S_j) + m j (u unit, c in Z_m; S_j = sum_{i<j} r^i), checked as
 *   homomorphisms on the generators (1,0), (0,1).  Table groups: all inner automorphisms g x g^-1.
 * Orbits of Aut on G\{e} give the representatives x.  For a representative x, the stabiliser G_x (automorphisms
 * fixing x, identity excluded) acts on unordered pairs {y,z} of G\{0,x}; the pairs are scanned in lexicographic order
 * and a pair is searched only if it is not yet marked; searching it marks all its G_x-images. So exactly the least pair
 * of each orbit is searched.  Automorphisms in the list need not form a group: the argument only uses that each is an
 * automorphism fixing 0 and x. */
static int check_hom_gens(const int *phi, const int *gl, int ng) {
    for (int t = 0; t < ng; t++) { int g = gl[t]; for (int h = 0; h < N; h++) if (phi[mul(g, h)] != mul(phi[g], phi[h])) return 0; }
    return 1;
}
static int *reps; static int nreps;
static int naut = 0, *au, *ac, *Sj;     /* meta: AUT list */
static int is_meta = 0;
static int build_aut_meta(void) {
    int m = M_, k = K_, r = R_;
    int gl[2] = { 1 % N, m % N };
    Sj = malloc(k * sizeof(int)); Sj[0] = 0; long rp = 1 % m;
    for (int j = 1; j < k; j++) { Sj[j] = (int)((Sj[j - 1] + rp) % m); rp = rp * r % m; }
    au = malloc(sizeof(int) * (size_t)m * m); ac = malloc(sizeof(int) * (size_t)m * m);
    int *phi = malloc(N * sizeof(int));
    for (int u = 1; u < m || (m == 1 && u == 1); u++) {
        if (m > 1 && gcd_i(u, m) != 1) continue;
        for (int c = 0; c < m; c++) {
            for (int j = 0; j < k; j++) for (int a = 0; a < m; a++) phi[a + m * j] = (int)(((long)u * a + (long)c * Sj[j]) % m) + m * j;
            if (!check_hom_gens(phi, gl, 2)) continue;
            au[naut] = u; ac[naut] = c; naut++;
        }
    }
    free(phi);
    int ntr = 0; for (int t = 0; t < naut; t++) if (au[t] == 1) ntr++;
    fprintf(stderr, "aut: |AUT| = %d verified (u,c) maps, %d of them translations (u=1)\n", naut, ntr);
    return naut;
}
static inline int meta_apply(int t, int y) {
    int a = y % M_, j = y / M_;
    return (int)(((long)au[t] * a + (long)ac[t] * Sj[j]) % M_) + M_ * j;
}
static inline int conj_apply(int g, int y) { return mul(mul(g, y), INV[g]); }

static void build_reps(void) {
    uf = malloc(N * sizeof(int)); for (int g = 0; g < N; g++) uf[g] = g;
    if (is_meta) {
        build_aut_meta();
        for (int t = 0; t < naut; t++) for (int g = 0; g < N; g++) uf_union(g, meta_apply(t, g));
    } else {
        for (int g = 1; g < N; g++) for (int y = 0; y < N; y++) uf_union(y, conj_apply(g, y));
        fprintf(stderr, "inner automorphisms: classes on G\\{e} computed\n");
    }
    reps = malloc(N * sizeof(int)); nreps = 0;
    int *seen = calloc(N, sizeof(int));
    for (int g = 1; g < N; g++) { int root = uf_find(g); if (!seen[root]) { seen[root] = 1; reps[nreps++] = g; } }
    free(seen);
    for (int g = 1; g < N; g++) if (uf_find(g) == uf_find(0)) { fprintf(stderr, "identity not fixed?\n"); exit(2); }
}

/* stabiliser of x: tags of the automorphisms fixing x (identity excluded) */
static int *stab; static int nstab;
static inline int act(int t, int y) { return is_meta ? meta_apply(t, y) : conj_apply(t, y); }
static void build_stab(int x) {
    nstab = 0;
    if (is_meta) {
        stab = realloc(stab, sizeof(int) * (size_t)(naut + 1));
        for (int t = 0; t < naut; t++) if (!(au[t] == 1 && ac[t] == 0) && meta_apply(t, x) == x) stab[nstab++] = t;
    } else {
        stab = realloc(stab, sizeof(int) * (size_t)(N + 1));
        for (int g = 1; g < N; g++) if (conj_apply(g, x) == x) stab[nstab++] = g;
    }
}

int main(int argc, char **argv) {
    if (argc < 6) { fprintf(stderr, "usage: exh meta M K R LIMIT TAG MAXSEC [D] | exh tab FILE LIMIT TAG MAXSEC [D]\n"); return 2; }
    int a = 1;
    if (!strcmp(argv[a], "meta")) { is_meta = 1; int mm = atoi(argv[a + 1]), kk = atoi(argv[a + 2]), rr = atoi(argv[a + 3]); a += 4; load_meta(mm, kk, rr); }
    else { load_tab(argv[a + 1]); a += 2; }
    long LIMIT = atol(argv[a]); snprintf(tag, sizeof tag, "%s", argv[a + 1]); double MAXSEC = atof(argv[a + 2]);
    if (argc > a + 3) D = atoi(argv[a + 3]);
    setup_inv();
    setup_cosets();
    build_reps();
    if (MAXSEC < 0) { printf("N=%d reps=%d aut=%d nH=%d R=%d\n", N, nreps, is_meta ? naut : N, nH, R); return 0; }
    Fb = malloc((size_t)2 * R * 8); NFb = malloc((size_t)2 * R * 8); Vb = malloc((size_t)2 * R * 8);
    uint16_t *visit = calloc((size_t)N * N, 2);

    char spath[600], hpath[600];
    snprintf(spath, sizeof spath, "state/%s.txt", tag);
    snprintf(hpath, sizeof hpath, "hits/%s.txt", tag);
    int start = 0, done = 0; long best = LIMIT; long long ev_prev = 0; double secs_prev = 0;
    FILE *sf = fopen(spath, "r");
    if (sf) {
        int nx, dn; long bb; long long ev; double sc;
        if (fscanf(sf, "next %d best %ld evals %lld secs %lf done %d", &nx, &bb, &ev, &sc, &dn) == 5) { start = nx; best = bb; ev_prev = ev; secs_prev = sc; done = dn; }
        fclose(sf);
    }
    if (done) { printf("ALREADY DONE tag=%s min=%ld\n", tag, best); return 0; }
    FILE *hf = fopen(hpath, "a");
    double t0 = now();
    printf("exh tag=%s N=%d nH=%d R=%d reps=%d start_rep=%d bound=%ld D=%d\n", tag, N, nH, R, nreps, start, best, D);
    fflush(stdout);
    int ri = start; int wr[5] = {0, 0, 0, 0, 0};
    for (; ri < nreps; ri++) {
        int x = reps[ri];
        unsigned short stamp = (unsigned short)(ri + 1);
        long long ev0 = evals; long before = best; long long orbits = 0;
        build_stab(x);
        for (int y = 1; y < N; y++) {
            if (y == x) continue;
            for (int z = y + 1; z < N; z++) {
                if (z == x) continue;
                if (visit[(size_t)y * N + z] == stamp) continue;
                visit[(size_t)y * N + z] = stamp;
                for (int t = 0; t < nstab; t++) {
                    int p = act(stab[t], y), q = act(stab[t], z); if (p > q) { int tmp = p; p = q; q = tmp; }
                    visit[(size_t)p * N + q] = stamp;
                }
                orbits++;
                volt[0] = 0; volt[1] = x; volt[2] = y; volt[3] = z;
                for (int i = 0; i < 4; i++) vinv[i] = INV[volt[i]];
                long c = cost(best);
                if (c <= best) {
                    int S[4] = { 0, x, y, z };
                    if (hf && c <= 6) fprintf(hf, "%ld 0 %d %d %d\n", c, x, y, z);
                    if (c < best) { best = c; printf("IMPROVED rep=%d cost=%ld S={0,%d,%d,%d}\n", ri, c, x, y, z); fflush(stdout); }
                    if (c <= 4 && !wr[c]) {
                        wr[c] = 1; char ep[600]; snprintf(ep, sizeof ep, "out/%s_c%ld.edges", tag, c);
                        write_edges(ep, S); printf("WROTE cost=%ld S={0,%d,%d,%d} %s\n", c, x, y, z, ep); fflush(stdout);
                    }
                }
            }
        }
        if (hf) fflush(hf);
        printf("rep %d/%d x=%d stab=%d best=%ld (was %ld) orbits=%lld rep_evals=%lld total=%lld t=%.1f\n", ri + 1, nreps, x, nstab, best, before,
               orbits, evals - ev0, evals, now() - t0); fflush(stdout);
        FILE *o = fopen(spath, "w");
        if (o) { fprintf(o, "next %d best %ld evals %lld secs %.1f done %d\n", ri + 1, best, ev_prev + evals, secs_prev + (now() - t0), ri + 1 == nreps); fclose(o); }
        if (now() - t0 > MAXSEC && ri + 1 < nreps) { ri++; break; }
    }
    if (hf) fclose(hf);
    if (ri >= nreps) printf("DONE tag=%s N=%d min=%ld (exact over all %d reps, evals=%lld)\n", tag, N, best, nreps, evals);
    else printf("PAUSED tag=%s next_rep=%d best=%ld evals=%lld\n", tag, ri, best, evals);
    fflush(stdout);
    return 0;
}
