/* twoch.c: exact 2-change neighbourhood of a tabu3 state (all pairs of single parameter changes on distinct slots).
 * Includes tabu3.c (same moves: element slots, coset slots, H, K). usage: twoch TABLE A PARFILE LO HI HISTFILE [OUT]
 * Pairs are enumerated by first index p in [LO, HI) of the single-change list and any later r > p. Writes
 * "cost count" lines (cost = 2*bad) to HISTFILE, prints best pair, and writes OUT if the best beats the base. */
#define main tabu3_main
#include "tabu3.c"
#undef main

typedef struct { int kind, b, i, v; } chg;   /* kind 0: par[b][i] = v; kind 1: hs = v; kind 2: ks = v */
static chg L[8192];
static int nL;
static int getv(chg c) { return c.kind == 0 ? par[c.b][c.i] : c.kind == 1 ? hs : ks; }
static void setv(chg c, int v) { if (c.kind == 0) par[c.b][c.i] = v; else if (c.kind == 1) hs = v; else ks = v; }
static int valid_set(chg c) { if (c.kind == 0 && is_elem(c.b)) return !dup_in_block(c.b, c.i, c.v); return 1; }
static int slot_id(chg c) { return c.kind == 0 ? c.b * 16 + c.i : 1000 + c.kind; }
static void show(chg c) {
    if (c.kind == 0) printf("slot(%d,%d)=%d", c.b, c.i, c.v); else printf("%s=%d", c.kind == 1 ? "H" : "K", c.v);
}
static long hist[65536];

int main(int argc, char **argv) {
    if (argc < 7) { fprintf(stderr, "usage: twoch TABLE A PARFILE LO HI HISTFILE [OUT]\n"); return 1; }
    FILE *f = fopen(argv[1], "r"); if (!f) return 1;
    if (fscanf(f, "%d", &m) != 1 || m > MAXM) return 1;
    T = malloc(sizeof(int) * m * m);
    for (int i = 0; i < m * m; i++) if (fscanf(f, "%d", &T[i]) != 1) return 1;
    fclose(f);
    q = m / 3; unw = getenv("UNW") != NULL;
    int a = atoi(argv[2]);
    nS[0] = a; nS[1] = 5 - a; nS[2] = 1; nS[3] = 5 - a; nS[4] = a; nS[5] = 1; nS[6] = 1; nS[7] = 1;
    for (int x = 0; x < m; x++) { int y = x, o = 1; while (y != 0) { y = MUL(y, x); o++; } ord_[x] = o; }
    enum_sub();
    for (int s = 0; s < nsub; s++) build_cosets(s);
    FILE *fi = fopen(argv[3], "r"); if (!fi) return 1;
    for (int b = 0; b < 8; b++) for (int i = 0; i < nS[b]; i++) if (fscanf(fi, "%d", &par[b][i]) != 1) return 1;
    int hg = 0, kg = 0;
    if (fscanf(fi, " H %d K %d", &hg, &kg) != 2) return 1;
    fclose(fi);
    for (int s = 0; s < nsub; s++) { if (subel[s][1] == hg || subel[s][2] == hg) hs = s; if (subel[s][1] == kg || subel[s][2] == kg) ks = s; }
    int lo = atoi(argv[4]), hi = atoi(argv[5]); const char *histfn = argv[6];
    int base = cost_now();
    /* single-change list from the base state */
    nL = 0;
    for (int b = 0; b < 8; b++) for (int i = 0; i < nS[b]; i++)
        for (int v = 0; v < m; v++) {
            if (v == par[b][i]) continue;
            chg c = {0, b, i, v};
            if (!valid_set(c)) continue;
            if (b == 2 || b == 5 || b == 6 || b == 7) {  /* keep the value even if equivalent: exact enumeration */ }
            L[nL++] = c;
        }
    for (int s = 0; s < nsub; s++) {
        if (s != hs) { chg c = {1, 0, 0, s}; L[nL++] = c; }
        if (s != ks) { chg c = {2, 0, 0, s}; L[nL++] = c; }
    }
    printf("base %d (bad %d) singles %d\n", base, base / 2, nL); fflush(stdout);
    if (hi > nL) hi = nL;
    double t0 = now();
    long npairs = 0, ninvalid = 0; int bestc = base + 1, bp = -1, br = -1;
    for (int p = lo; p < hi; p++) {
        chg P = L[p];
        if (!valid_set(P)) continue;
        int oldp = getv(P); setv(P, P.v);
        for (int r = p + 1; r < nL; r++) {
            chg R = L[r];
            if (slot_id(R) == slot_id(P)) continue;
            if (!valid_set(R)) { ninvalid++; continue; }
            int oldr = getv(R); setv(R, R.v);
            int c = cost_now();
            setv(R, oldr);
            npairs++;
            if (c < 65536) hist[c]++;
            if (c < bestc) { bestc = c; bp = p; br = r; }
        }
        setv(P, oldp);
    }
    FILE *hf = fopen(histfn, "w");
    if (hf) { for (int c = 0; c < 65536; c++) if (hist[c]) fprintf(hf, "%d %ld\n", c, hist[c]); fclose(hf); }
    printf("chunk [%d,%d) pairs %ld invalid %ld time %.1f\n", lo, hi, npairs, ninvalid, now() - t0);
    printf("best pair cost %d (bad %d)", bestc, bestc / 2);
    if (bp >= 0) { printf(": "); show(L[bp]); printf(" + "); show(L[br]); }
    printf("\n");
    if (argc > 7 && bp >= 0 && bestc < base) {
        setv(L[bp], L[bp].v); setv(L[br], L[br].v);
        cost_now(); write_edges(argv[7]);
        printf("wrote %s\n", argv[7]);
    }
    return 0;
}
