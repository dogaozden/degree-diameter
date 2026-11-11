/* ---------------- f15 FINISH: exact meet-in-the-middle hole test + greedy hole-coverage slot replacement ----------------
 * For odd D the B-type holes (cost of H(G,S), BHOLE clear) are the elements g with g not in G Q^k, k = (D-3)/2,
 * Q = G^-1 G (G = S, or S^-1 for BHOLE).  With k = 4 (D = 11): g in G Q2 Q2 iff exists s in G, u in Q2 with
 * (s u)^-1 g in Q2, so one exact test costs |G| |Q2| products (7776 at d = 6).  This is used as a prefilter: a candidate
 * orbit for slot j is scored by the number of holes of the reduced state (S without slot j) it fails to cover; only the
 * best-scoring candidate of each batch gets a full BFS evaluation. */
typedef struct { u64 *bit; el *q2; i64 *q2i; int nq2u; el g[MAXD]; int dd; } MI;
static MI MIA, MIB; static int MI_CAP;
static void mi_init(MI *m) { m->bit = calloc(NG / 64 + 2, sizeof(u64)); m->q2 = malloc(sizeof(el) * MI_CAP); m->q2i = malloc(sizeof(i64) * MI_CAP); m->nq2u = 0; }
static void mi_prep(MI *m, const el *g, int dd) {
    for (int i = 0; i < m->nq2u; i++) { i64 k = m->q2i[i]; m->bit[k >> 6] &= ~(1ULL << (k & 63)); }
    m->nq2u = 0; m->dd = dd; memcpy(m->g, g, sizeof(el) * dd);
    el gi[MAXD]; for (int a = 0; a < dd; a++) gi[a] = einv(g[a]);
    static el Q1[MAXD * MAXD]; int nq1 = 0;
    for (int a = 0; a < dd; a++) for (int b = 0; b < dd; b++) Q1[nq1++] = emul(gi[a], g[b]);
    for (int x = 0; x < nq1; x++) for (int y = 0; y < nq1; y++) {
        el q = emul(Q1[x], Q1[y]); i64 k = eidx(q);
        if (!((m->bit[k >> 6] >> (k & 63)) & 1)) { m->bit[k >> 6] |= 1ULL << (k & 63); if (m->nq2u < MI_CAP) { m->q2[m->nq2u] = q; m->q2i[m->nq2u++] = k; } }
    }
}
static int mi_covered(const MI *m, el x) {   /* x in G Q2 Q2 ? */
    for (int a = 0; a < m->dd; a++) for (int u = 0; u < m->nq2u; u++) {
        el w = emul(m->g[a], m->q2[u]); el y = emul(einv(w), x); i64 k = eidx(y);
        if ((m->bit[k >> 6] >> (k & 63)) & 1) return 1;
    }
    return 0;
}
static void tables_for(int j, el s) {
    TT[j] = s;
    for (i64 v = 0; v < R; v++) {
        int a, c; rowv(v, &a, &c);
        el rep; rep.a = a; rep.c = c; rep.z = 0;
        if (a) { rep.b = 0; rep.d = INV[a]; } else { rep.b = md(-(i64)INV[c]); rep.d = 0; }
        el m = emul(s, rep);
        i64 v2 = vrow(m.a, m.c); i64 cr = crt(tco(m), s.z);
        FR[j][v] = (u32)v2; FC[j][v] = (u32)cr;
        PS[j][v2] = ((u64)v << 32) | (u64)(L - cr);
        PI[j][v] = ((u64)v2 << 32) | (u64)(cr ? cr : L);
    }
}
static void finish_loop(const char *out, double secs, int K) {
    MI_CAP = 1; for (int i = 0; i < 4; i++) MI_CAP *= d; if (MI_CAP > NG + 1) MI_CAP = (int)(NG + 1);
    mi_init(&MIA); mi_init(&MIB);
    int TARGFIN = 0; (void)TARGFIN;
    i64 *FL = malloc(sizeof(i64) * UCAP), *RL = malloc(sizeof(i64) * UCAP);
    int nf = 0; i64 c = cost(NOBOUND, FL, UCAP, &nf);
    i64 best = c; el bestS[MAXD]; memcpy(bestS, S, sizeof(el) * d);
    char bestfile[1024]; snprintf(bestfile, sizeof bestfile, "%s.best", out);
    double t0 = now(); i64 it = 0, nfull = 0; double TF = getenv("TF") ? atof(getenv("TF")) : 1.0;
    fprintf(stderr, "finish: start cost %lld (holes %d)\n", (long long)c, nf);
    while (!stop_flag && now() - t0 < secs && best > 0) {
        it++;
        int j = (int)(rnd() % OM);
        el raw[MAXD]; int nr = 0;
        for (int u = 0; u < d; u++) if (u < ostart(j) || u >= ostart(j) + OK_) raw[nr++] = S[u];
        el bi = einv(raw[0]); el RG[MAXD];
        for (int k = 0; k < nr; k++) RG[k] = emul(raw[k], bi);
        d = nr; for (int k = 0; k < nr; k++) tables_for(k, RG[k]);
        int nrh = 0; i64 rc = cost(NOBOUND, RL, UCAP, &nrh);
        if (rc < 0) { d = OF + OK_ * OM; for (int u = 0; u < d; u++) make_tables(u); continue; }
        /* holes of the reduced state: RL (BHOLE flag as usual) */
        el keep[MAXD]; memcpy(keep, S + ostart(j), sizeof(el) * OK_);
        el bestO[MAXD]; int bestf = 1 << 30, have = 0; int ncand = 0;
        for (int t = 0; t < K && !stop_flag; t++) {
            el o[MAXD]; if (!random_orbit(j, o)) continue;
            ncand++;
            el F[MAXD]; memcpy(F, RG, sizeof(el) * nr); for (int i = 0; i < OK_; i++) F[nr + i] = emul(o[i], bi);
            /* normalised set F (size d) and its inverse */
            el Fi[MAXD]; for (int a = 0; a < d; a++) Fi[a] = einv(F[a]);
            mi_prep(&MIA, F, d); mi_prep(&MIB, Fi, d);
            int fails = 0; int off = nrh ? (int)(rnd() % nrh) : 0;
            for (int ii = 0; ii < nrh; ii++) {
                i64 h = RL[(ii + off) % nrh]; el x = eofidx(h & ~BHOLE);
                if (!mi_covered((h & BHOLE) ? &MIB : &MIA, x)) { fails++; if (fails > bestf) break; }
            }
            if (fails <= bestf) { bestf = fails; memcpy(bestO, o, sizeof(el) * OK_); have = 1; }
        }
        d = OF + OK_ * OM; for (int u = 0; u < d; u++) make_tables(u);
        if (!have) continue;
        memcpy(S + ostart(j), bestO, sizeof(el) * OK_); for (int i = 0; i < OK_; i++) retab(j);
        for (int u = 0; u < d; u++) make_tables(u);
        i64 c2 = cost(NOBOUND, FL, UCAP, &nf); nfull++;
        int acc = c2 <= c || exp((double)(c - c2) / TF) > (double)(rnd() % 1000000) / 1e6;
        if (acc) { c = c2; if (c < best) { best = c; memcpy(bestS, S, sizeof(el) * d); write_sol(bestfile, bestS); } }
        else { memcpy(S + ostart(j), keep, sizeof(el) * OK_); for (int u = 0; u < d; u++) make_tables(u); }
        fprintf(stderr, "t=%.0f it=%lld slot=%d reduced_holes=%d cands=%d bestfail=%d cost_new=%lld cost=%lld best=%lld %s\n",
                now() - t0, (long long)it, j, nrh, ncand, bestf, (long long)c2, (long long)c, (long long)best, acc ? "acc" : "rej");
    }
    memcpy(S, bestS, sizeof(el) * d); for (int u = 0; u < d; u++) make_tables(u);
    i64 cf = cost(NOBOUND, FL, UCAP, &nf);
    printf("FINISH d=%d D=%d group=%s x Z_%lld N=%lld vertices=%lld best=%lld reeval=%lld iters=%lld full_evals=%lld time=%.1f\n",
           d, D, SPEC, (long long)NC, (long long)NG, (long long)(2 * NG), (long long)best, (long long)cf, (long long)it, (long long)nfull, now() - t0);
    if (cf == 0) { write_sol(out, S); printf("wrote %s\n", out); }
}

