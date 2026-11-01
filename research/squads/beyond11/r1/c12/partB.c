/* ---------------- SD (c12): self-dual symmetric S for odd D ----------------
 * tau(M,z) = (M^T, z) is an anti-automorphism of G.  alpha = conjugation by g with g^T g = s I (s = +-1, so
 * alpha tau = tau alpha) times z -> r z.  If tau(S) = S then gamma(x) = tau(x)^-1 is an automorphism with
 * gamma(S) = S^-1, so H(G,S^-1) = H(G,S) (same sides, (e,A) fixed) and the odd-D cost is 2 x the one-sided cost.
 * S = {e} + H-orbits, H = <alpha, tau>; slot k is one H-orbit of size SDSIZES[k] (1, 2, 3 or 6). */
static int NSLOT;                       /* slot 0 = {e} (position 0), slots 1.. = H-orbits */
static int SLOTPOS[MAXD], SLOTSZ[MAXD];
static i64 NLIST[4]; static el *SZLIST[4];   /* all elements whose H-orbit has size 1, 2, 3 */
#define LCAP (1 << 21)
static inline el tau(el x) { el t = {x.a, x.c, x.b, x.d, x.z}; return canon(t); }
static int horbit(el x, el *o) {   /* H-orbit of x (size <= 6, 7 if the orbit is larger) */
    int n = 1; o[0] = x;
    for (int i = 0; i < n; i++) {
        el c[2] = {alpha(o[i]), tau(o[i])};
        for (int k = 0; k < 2; k++) { int f = 0;
            for (int u = 0; u < n && !f; u++) f = eeq(o[u], c[k]);
            if (!f) { if (n == 6) return 7; o[n++] = c[k]; } }
    }
    return n;
}
static int hfree(const el *o, int sz, int k) {   /* the H-orbit o (size sz) avoids every generator outside slot k */
    for (int i = 0; i < sz; i++) for (int u = 0; u < d; u++) {
        if (u >= SLOTPOS[k] && u < SLOTPOS[k] + SLOTSZ[k]) continue;
        if (eeq(S[u], o[i])) return 0;
    }
    return 1;
}
static void build_lists(void) {
    for (int s = 1; s <= 3; s++) { NLIST[s] = 0; SZLIST[s] = NULL; }
    for (int s = 1; s <= 3; s++) for (int k = 1; k < NSLOT; k++) if (SLOTSZ[k] == s && !SZLIST[s]) SZLIST[s] = malloc(sizeof(el) * LCAP);
    el o[8];
    for (i64 g = 0; g < NG; g++) {
        el x = canon(eofidx(g)); if (eeq(x, E_ID)) continue;
        int n = horbit(x, o);
        if (n <= 3 && SZLIST[n] && NLIST[n] < LCAP) SZLIST[n][NLIST[n]++] = x;
    }
}
static int random_hslot(int k, el *o) {   /* random H-orbit of the slot's size, avoiding the other generators */
    int sz = SLOTSZ[k];
    for (int t = 0; t < 4000000; t++) {
        el x;
        if (sz == 6) x = randel();
        else { if (!NLIST[sz]) return 0; x = SZLIST[sz][rnd() % (u64)NLIST[sz]]; }
        if (horbit(x, o) == sz && hfree(o, sz, k)) return 1;
    }
    return 0;
}
static void choose_alpha_sd(void) {   /* g in SL(2,p) of trace +-1 with g^T g = +-I (so tau alpha = alpha tau) */
    int *rt = malloc(sizeof(int) * P);
    for (int i = 0; i < P; i++) rt[i] = -1;
    for (int x = 0; x < P; x++) rt[(i64)x * x % P] = x;
    el *LA = malloc(sizeof(el) * 4 * P + 8), *LB = malloc(sizeof(el) * 4 * P + 8);
    for (int si = 0; si < 2; si++) {
        int s = si ? P - 1 : 1, na = 0, nb = 0;
        for (int a = 0; a < P; a++) { int t = md((i64)s - (i64)a * a); if (rt[t] < 0) continue;
            LA[na++] = (el){a, 0, rt[t], 0, 0}; if (rt[t]) LA[na++] = (el){a, 0, P - rt[t], 0, 0}; }
        for (int b = 0; b < P; b++) { int t = md((i64)s - (i64)b * b); if (rt[t] < 0) continue;
            LB[nb++] = (el){0, b, 0, rt[t], 0}; if (rt[t]) LB[nb++] = (el){0, b, 0, P - rt[t], 0}; }
        for (int i = 0; i < na; i++) for (int j = 0; j < nb; j++) {
            int a = LA[i].a, c = LA[i].c, b = LB[j].b, dd = LB[j].d;
            if (md((i64)a * b + (i64)c * dd) != 0) continue;
            if (md((i64)a * dd - (i64)b * c) != 1) continue;
            int tr = (a + dd) % P;
            if (tr != 1 && tr != P - 1) continue;
            AG = canon((el){a, b, c, dd, 0}); AGI = einv(AG);
            fprintf(stderr, "alpha: g=(%d,%d,%d,%d) trace %d, g^T g = %s I\n", a, b, c, dd, tr, si ? "-" : "+");
            free(rt); free(LA); free(LB); return;
        }
    }
    fprintf(stderr, "no orthogonal-type g of trace +-1 in SL(2,%d)\n", P); exit(2);
}
/* cost of the current S (odd D): the one-sided count, doubled.  bound is in doubled units. */
static i64 cost_sd(i64 bound, i64 *unc, int ucap, int *nunc) {
    INVS = 0;
    i64 b1 = bound == NOBOUND ? NOBOUND : (bound + 1) / 2;
    i64 c = cost1(b1, unc, ucap, nunc);
    return c < 0 ? -1 : 2 * c;
}
static void retab_slot(int k) { for (int i = 0; i < SLOTSZ[k]; i++) make_tables(SLOTPOS[k] + i); }
static void retab(int j) { retab_slot(j); }
