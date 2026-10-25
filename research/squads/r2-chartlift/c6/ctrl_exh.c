/* Voltage-lift controllers for route-chart lifts at diameter 5 (any k <= 8).
   Base: k-regular bipartite multigraph on r + r vertices (file: "r" then r*k lines "i j [colour]"); colours are a proper
   k-edge-colouring (computed by peeling perfect matchings if not given).  Group G: Cayley table file ("g" then g*g
   entries x*y), or "cyclic:N".  Controller vertex (a_i, x), (b_j, y); base edge e = (a_i, b_j) with voltage v_e gives
   (a_i, x) ~ (b_j, v_e x).  Chart flags file (from chartflags.py): k; then sing[A] k^4 ints, sing[B] k^4 ints
   (1 = singular nonbacktracking pattern); pen[A] k^2, pen[B] k^2 (1 = one-detour pencil complete); diagA diagB
   (1 = closed backtracking walks cover the fibre).  "universal" = no singular pattern, every pencil complete, no diagonal.
   A same-side controller pair (u, u') is counted covered iff
     u' != u is the end of a length-2 walk whose colour pair has a complete pencil, or
     u' is the end of a nonbacktracking length-4 walk with a nonsingular pattern (u' = u: a 4-cycle), or
     u' = u and the side's diagonal flag is set.
   Cost = uncovered (base vertex, target) pairs over both sides (each is a whole G-orbit of controller pairs).
   usage: ctrl_search BASE GROUP FLAGS seconds seed [out_prefix]
   Writes out_prefix.volt (voltages) and out_prefix.ctrl ("m" then lines "a b colour", a,b in 0..m-1) when cost 0. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <time.h>
#include <stdint.h>
#include <time.h>
static double wall(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return t.tv_sec + 1e-9 * t.tv_nsec; }
static uint64_t rs = 88172645463325252ULL;
static inline uint64_t xr(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
#define MAXE 256
int r, k, ne, EA[MAXE], EB[MAXE], col[MAXE], g, *T, *Inv, eid, istree[MAXE], volt[MAXE];
unsigned char sing[2][8][8][8][8], pen[2][8][8], diag[2];
typedef struct { int len, e[4], end; } Walk;
Walk *W[2][64]; int nw[2][64];
unsigned char *hit;
static inline int mul(int a, int b) { return T[a * g + b]; }
static int walk_elt(int side, const Walk *w) {
    const int *E = w->e;
    if (side == 0) { if (w->len == 2) return mul(Inv[volt[E[1]]], volt[E[0]]);
        return mul(Inv[volt[E[3]]], mul(volt[E[2]], mul(Inv[volt[E[1]]], volt[E[0]]))); }
    if (w->len == 2) return mul(volt[E[1]], Inv[volt[E[0]]]);
    return mul(volt[E[3]], mul(Inv[volt[E[2]]], mul(volt[E[1]], Inv[volt[E[0]]]))); }
long cost_detail[2];
static long cost(void) {
    long c = 0; cost_detail[0] = cost_detail[1] = 0;
    for (int s = 0; s < 2; s++) for (int i = 0; i < r; i++) {
        memset(hit, 0, (size_t)r * g);
        for (int t = 0; t < nw[s][i]; t++) { const Walk *w = &W[s][i][t]; int x = walk_elt(s, w);
            if (w->len == 2 && w->end == i && x == eid) continue;   /* a length-2 walk back to u never covers u */
            hit[(size_t)w->end * g + x] = 1; }
        if (diag[s]) hit[(size_t)i * g + eid] = 1;
        long u = 0; for (long t = 0; t < (long)r * g; t++) u += !hit[t];
        c += u; cost_detail[s] += u; }
    return c; }
static int parallel_ok(void) { for (int a = 0; a < ne; a++) for (int b = a + 1; b < ne; b++) if (EA[a] == EA[b] && EB[a] == EB[b] && volt[a] == volt[b]) return 0; return 1; }
int used[MAXE], matchB[64], visB[64];
static int aug(int a) { for (int e = 0; e < ne; e++) if (!used[e] && EA[e] == a && !visB[EB[e]]) { visB[EB[e]] = 1;
        if (matchB[EB[e]] < 0 || aug(EA[matchB[EB[e]]])) { matchB[EB[e]] = e; return 1; } } return 0; }
static void colour(void) {
    memset(used, 0, sizeof used);
    for (int c = 0; c < k; c++) { for (int j = 0; j < r; j++) matchB[j] = -1;
        for (int a = 0; a < r; a++) { memset(visB, 0, sizeof visB); if (!aug(a)) { printf("colouring failed\n"); exit(9); } }
        for (int j = 0; j < r; j++) { col[matchB[j]] = c; used[matchB[j]] = 1; } } }
int main(int argc, char **argv) {
    if (argc < 6) { fprintf(stderr, "usage: ctrl_search BASE GROUP FLAGS seconds seed [out_prefix]\n"); return 1; }
    /* base */
    FILE *f = fopen(argv[1], "r"); if (!f || fscanf(f, "%d", &r) != 1) return 2;
    char line[256]; ne = 0; int given_col = 1; if (!fgets(line, sizeof line, f)) return 2;
    while (fgets(line, sizeof line, f)) { int a, b, c; int got = sscanf(line, "%d %d %d", &a, &b, &c);
        if (got < 2) continue; EA[ne] = a; EB[ne] = b; if (got == 3) col[ne] = c; else given_col = 0; ne++; }
    fclose(f); k = ne / r; if (k * r != ne || k > 8) { printf("bad base\n"); return 3; }
    if (!given_col) colour();
    /* group */
    if (!strncmp(argv[2], "cyclic:", 7)) { g = atoi(argv[2] + 7); T = malloc(sizeof(int) * g * g);
        for (int a = 0; a < g; a++) for (int b = 0; b < g; b++) T[a * g + b] = (a + b) % g; }
    else { f = fopen(argv[2], "r"); if (!f || fscanf(f, "%d", &g) != 1) return 4; T = malloc(sizeof(int) * g * g);
        for (int i = 0; i < g * g; i++) if (fscanf(f, "%d", &T[i]) != 1) return 5; fclose(f); }
    Inv = malloc(sizeof(int) * g);
    for (int i = 0; i < g; i++) { int ok = 1; for (int j = 0; j < g; j++) if (T[i * g + j] != j) { ok = 0; break; } if (ok) eid = i; }
    for (int i = 0; i < g; i++) for (int j = 0; j < g; j++) if (T[i * g + j] == eid) Inv[i] = j;
    /* chart flags */
    if (!strcmp(argv[3], "universal")) { memset(sing, 0, sizeof sing); for (int s = 0; s < 2; s++) for (int i = 0; i < k; i++) for (int j = 0; j < k; j++) pen[s][i][j] = 1; diag[0] = diag[1] = 0; }
    else { f = fopen(argv[3], "r"); int kk; if (!f || fscanf(f, "%d", &kk) != 1 || kk != k) { printf("flags k mismatch\n"); return 6; }
        for (int s = 0; s < 2; s++) for (int a = 0; a < k; a++) for (int b = 0; b < k; b++) for (int c = 0; c < k; c++) for (int d = 0; d < k; d++) { int x; if (fscanf(f, "%d", &x) != 1) return 7; sing[s][a][b][c][d] = x; }
        for (int s = 0; s < 2; s++) for (int a = 0; a < k; a++) for (int b = 0; b < k; b++) { int x; if (fscanf(f, "%d", &x) != 1) return 7; pen[s][a][b] = x; }
        for (int s = 0; s < 2; s++) { int x; if (fscanf(f, "%d", &x) != 1) return 7; diag[s] = x; } fclose(f); }
    double secs = atof(argv[4]); rs ^= (uint64_t)atoll(argv[5]) * 0x9E3779B97F4A7C15ULL; xr();
    const char *out = argc > 6 ? argv[6] : NULL;
    /* spanning tree (gauge) */
    int seen[128] = {0}, qq[128], h = 0, t = 0; seen[0] = 1; qq[t++] = 0;
    while (h < t) { int x = qq[h++];
        for (int i = 0; i < ne; i++) { int a = EA[i], b = r + EB[i], y = -1;
            if (x == a && !seen[b]) y = b; else if (x == b && !seen[a]) y = a;
            if (y >= 0) { seen[y] = 1; qq[t++] = y; istree[i] = 1; } } }
    if (t != 2 * r) { printf("base disconnected\n"); return 8; }
    /* walks */
    for (int s = 0; s < 2; s++) for (int i = 0; i < r; i++) {
        W[s][i] = malloc(sizeof(Walk) * 4096); int n = 0;
        int *X = s ? EB : EA, *Y = s ? EA : EB;   /* start side endpoint array X, other side Y */
        for (int e1 = 0; e1 < ne; e1++) if (X[e1] == i)
        for (int e2 = 0; e2 < ne; e2++) if (Y[e2] == Y[e1] && e2 != e1) {
            if (pen[s][col[e1]][col[e2]]) { Walk w = {2, {e1, e2, 0, 0}, X[e2]}; W[s][i][n++] = w; }
            for (int e3 = 0; e3 < ne; e3++) if (e3 != e2 && X[e3] == X[e2])
            for (int e4 = 0; e4 < ne; e4++) if (e4 != e3 && Y[e4] == Y[e3]) {
                if (sing[s][col[e1]][col[e2]][col[e3]][col[e4]]) continue;
                Walk w = {4, {e1, e2, e3, e4}, X[e4]}; W[s][i][n++] = w; } }
        nw[s][i] = n; }
    hit = malloc((size_t)r * g + 1);
    if (getenv("VOLT")) { char *p = getenv("VOLT"); for (int i = 0; i < ne; i++) { volt[i] = (int)strtol(p, &p, 10); if (*p == ',') p++; }
        long c = cost(); printf("given voltages: cost=%ld (A %ld, B %ld) parallel_ok=%d\n", c, cost_detail[0], cost_detail[1], parallel_ok());
        if (getenv("DEBUG")) for (int s = 0; s < 2; s++) for (int i = 0; i < r; i++) {
            memset(hit, 0, (size_t)r * g);
            for (int t = 0; t < nw[s][i]; t++) { const Walk *w = &W[s][i][t]; int x = walk_elt(s, w);
                if (w->len == 2 && w->end == i && x == eid) continue; hit[(size_t)w->end * g + x] = 1; }
            if (diag[s]) hit[(size_t)i * g + eid] = 1;
            for (int t = 0; t < r * g; t++) if (!hit[t]) printf("  uncovered: side %c base vertex %d -> base vertex %d, group element %d%s\n", s ? 'B' : 'A', i, t / g, t % g, (t / g == i && t % g == eid) ? "  (diagonal)" : ""); }
        if (out) { char fn[512]; snprintf(fn, sizeof fn, "%s.ctrl", out); FILE *o = fopen(fn, "w"); fprintf(o, "%d\n", r * g);
            for (int i = 0; i < ne; i++) for (int x = 0; x < g; x++) fprintf(o, "%d %d %d\n", EA[i] * g + x, EB[i] * g + mul(volt[i], x), col[i]);
            fclose(o); }
        return 0; }
    /* PIN="e:v,e:v": fix edge e's voltage to group element v (e.g. to force 4-cycles); pinned edges are never moved */
    int pinned[MAXE] = {0}, pinval[MAXE] = {0};
    if (getenv("PIN")) { char *p = getenv("PIN"); while (*p) { int e = (int)strtol(p, &p, 10); if (*p == ':') p++; int v = (int)strtol(p, &p, 10); if (e >= 0 && e < ne) { pinned[e] = 1; pinval[e] = v; } if (*p == ',') p++; else break; } }
    int free_e[MAXE], nf = 0; for (int i = 0; i < ne; i++) if (!istree[i] && !pinned[i]) free_e[nf++] = i;
    /* EXH=1 (card c6): exhaustive scan of every voltage assignment to the free edges; tree edges stay eid (gauge). */
    if (getenv("EXH")) {
        double nd = 1; for (int j = 0; j < nf; j++) nd *= g;
        if (nd > 4e9) { printf("EXH too many assignments %.3g\n", nd); return 10; }
        int dig[MAXE] = {0}, bestv[MAXE], firstz[MAXE], haszero = 0;
        long cmin = -1, nzero = 0, nvalid = 0;
        for (int i = 0; i < ne; i++) volt[i] = eid;
        for (;;) {
            for (int j = 0; j < nf; j++) volt[free_e[j]] = dig[j];
            if (parallel_ok()) { long c = cost(); nvalid++;
                if (cmin < 0 || c < cmin) { cmin = c; memcpy(bestv, volt, sizeof volt); }
                if (c == 0) { nzero++; if (!haszero) { haszero = 1; memcpy(firstz, volt, sizeof volt); } } }
            int j = 0; while (j < nf) { if (++dig[j] < g) break; dig[j] = 0; j++; }
            if (j == nf) break; }
        printf("EXH r=%d k=%d g=%d m=%d free=%d valid=%ld min_cost=%ld zero_count=%ld\n", r, k, g, r * g, nf, nvalid, cmin, nzero);
        printf("EXH min_volt="); for (int i = 0; i < ne; i++) printf("%d%c", bestv[i], i + 1 < ne ? ',' : '\n');
        if (haszero) { memcpy(volt, firstz, sizeof volt); cost();
            printf("EXH first_zero_volt="); for (int i = 0; i < ne; i++) printf("%d%c", firstz[i], i + 1 < ne ? ',' : '\n');
            if (out) { char fn[512]; snprintf(fn, sizeof fn, "%s.volt", out); FILE *o = fopen(fn, "w");
                fprintf(o, "%d %d %d\n", r, k, g); for (int i = 0; i < ne; i++) fprintf(o, "%d %d %d %d\n", EA[i], EB[i], col[i], firstz[i]); fclose(o);
                snprintf(fn, sizeof fn, "%s.ctrl", out); o = fopen(fn, "w"); fprintf(o, "%d\n", r * g);
                for (int i = 0; i < ne; i++) for (int x = 0; x < g; x++) fprintf(o, "%d %d %d\n", EA[i] * g + x, EB[i] * g + mul(firstz[i], x), col[i]);
                fclose(o); } }
        return 0; }
    long best = -1; int bv[MAXE]; double t0 = wall(); long it = 0; int restarts = 0;
    while ((wall() - t0) < secs && best != 0) {
        restarts++;
        do { for (int i = 0; i < ne; i++) volt[i] = pinned[i] ? pinval[i] : (istree[i] ? eid : (int)(xr() % g)); } while (!parallel_ok());
        long c = cost(); if (best < 0 || c < best) { best = c; memcpy(bv, volt, sizeof volt); }
        double T0 = 1.0 + 0.02 * c; long stall = 0;
        while (stall < 200000 && best != 0 && (wall() - t0) < secs) {
            it++; int ei = free_e[xr() % nf], old = volt[ei]; volt[ei] = xr() % g;
            if (!parallel_ok()) { volt[ei] = old; continue; }
            long c2 = cost(); double TT = T0 * exp(-(double)stall / 30000.0) + 0.3;
            if (c2 <= c || exp((c - c2) / TT) > (double)(xr() % 1000000) / 1e6) { if (c2 < c) stall = 0; else stall++; c = c2;
                if (c < best) { best = c; memcpy(bv, volt, sizeof volt); } }
            else { volt[ei] = old; stall++; } } }
    memcpy(volt, bv, sizeof volt); cost();
    printf("r=%d k=%d g=%d m=%d best_cost=%ld (A %ld, B %ld) iters=%ld restarts=%d volt=", r, k, g, r * g, best, cost_detail[0], cost_detail[1], it, restarts);
    for (int i = 0; i < ne; i++) printf("%d%c", bv[i], i + 1 < ne ? ',' : '\n');
    if (out && (best == 0 || getenv("WRITEBEST"))) { char fn[512];
        snprintf(fn, sizeof fn, "%s.volt", out); FILE *o = fopen(fn, "w");
        fprintf(o, "%d %d %d\n", r, k, g); for (int i = 0; i < ne; i++) fprintf(o, "%d %d %d %d\n", EA[i], EB[i], col[i], bv[i]); fclose(o);
        snprintf(fn, sizeof fn, "%s.ctrl", out); o = fopen(fn, "w"); fprintf(o, "%d\n", r * g);
        for (int i = 0; i < ne; i++) for (int x = 0; x < g; x++) fprintf(o, "%d %d %d\n", EA[i] * g + x, EB[i] * g + mul(bv[i], x), col[i]);
        fclose(o); }
    return 0; }
