import re,sys
src = open('/home/user/degree-diameter/research/squads/sd5c-r1/c8/fsd_c8.c').read()
def rep(old, new, cnt=1):
    global src
    c = src.count(old)
    if c != cnt:
        sys.exit("count mismatch (%d vs %d) for: %r" % (c, cnt, old[:80]))
    src = src.replace(old, new)

# NG = max generators
rep("static int hkind;", "#define NG 5\nstatic int hkind;")
# product-kind globals after inv declaration
rep("static int *inv;", "static int *inv;\nstatic int *T1, *T2, *PH1, *PH2, nh1, nh2, pm1, pk1, pr1, pm2, pk2, pr2;")
# gmul branch for prod
rep("static inline int gmul(int a, int b) {\n    if (hkind == 0 || hkind == 3) {",
    "static inline int gmul(int a, int b) {\n"
    "    if (hkind == 4) { int h1 = T1[PH1[a] * nh1 + PH1[b]], h2 = T2[PH2[a] * nh2 + PH2[b]]; int l = EL[a] + EL[b]; if (l >= n3) l -= n3; return (h1 * nh2 + h2) * n3 + l; }\n"
    "    if (hkind == 0 || hkind == 3) {")
# coords
rep("static void coords(int e, char *buf) {\n",
    "static void coords(int e, char *buf) {\n    if (hkind == 4) { sprintf(buf, \"%d,%d,%d\", PH1[e], PH2[e], EL[e]); return; }\n")
# keyof: FNV hash over all generator images (5 generators do not fit in 64 bits)
rep("static uint64_t keyof(const int *img) { uint64_t kk = 0; for (int g = 0; g < ngen; g++) kk = kk << 16 | (uint64_t)img[g]; return kk; }",
    "static uint64_t keyof(const int *img) { uint64_t h = 1469598103934665603ULL; for (int g = 0; g < ngen; g++) { h ^= (uint64_t)(uint32_t)img[g]; h *= 1099511628211ULL; } return h; }")
# generator-count-dependent arrays
src = src.replace("int im[3]", "int im[NG]").replace("gens[3]", "gens[NG]").replace("img[3]", "img[NG]")
rep("memcpy(cand[ncand].img, img, sizeof(int) * 3);", "memcpy(cand[ncand].img, img, sizeof(int) * NG);")
src = src.replace("sizeof(int) * 3)", "sizeof(int) * NG)")
# meta_table + fac_auts helpers (before the group generator array declaration)
helpers = r'''static int *meta_table(int m, int k, int r, int **ivout) {     /* multiplication table of C_m : C_k, (i,j)(a,b) = (i + r^j a, j + b) */
    int nhs = m * k; int *T = malloc(sizeof(int) * (size_t)nhs * nhs), *iv = malloc(sizeof(int) * nhs);
    if (ipow(r, k, m) != 1 % m) { fprintf(stderr, "need r^k = 1 mod m (factor)\n"); exit(2); }
    for (int h = 0; h < nhs; h++) { int i = h / k, j = h % k; int rj = ipow(r, j, m);
        for (int h2 = 0; h2 < nhs; h2++) { int a = h2 / k, b = h2 % k;
            int ri = (int)((i + (long long)rj * a) % m), rjj = (j + b) % k; T[(size_t)h * nhs + h2] = ri * k + rjj; } }
    for (int h = 0; h < nhs; h++) for (int h2 = 0; h2 < nhs; h2++) if (T[(size_t)h * nhs + h2] == 0) iv[h] = h2;
    *ivout = iv; return T;
}
static int ngen, gens[NG];'''
rep("static int ngen, gens[NG];", helpers)
# build_group: prod branch
rep("    } else { fprintf(stderr, \"unknown group kind %s\\n\", argv[1]); exit(2); }",
"""    } else if (!strcmp(argv[1], "prod")) {
        /* prod m1 k1 r1 m2 k2 r2 n3 : (C_m1 : C_k1) x (C_m2 : C_k2) x C_n3 (two factors as in meta, both may be non-abelian) */
        if (argc < 9) { fprintf(stderr, "usage: prod m1 k1 r1 m2 k2 r2 n3\\n"); exit(2); }
        hkind = 4; pm1 = atoi(argv[2]); pk1 = atoi(argv[3]); pr1 = atoi(argv[4]); pm2 = atoi(argv[5]); pk2 = atoi(argv[6]); pr2 = atoi(argv[7]);
        n3 = atoi(argv[8]);
        int *iv1, *iv2; T1 = meta_table(pm1, pk1, pr1 < 0 ? 0 : pr1, &iv1); T2 = meta_table(pm2, pk2, pr2 < 0 ? 0 : pr2, &iv2);
        nh1 = pm1 * pk1; nh2 = pm2 * pk2; nh = nh1 * nh2; n = nh * n3;
        if (n >= 65536) { fprintf(stderr, "n = %d too large\\n", n); exit(2); }
        PH1 = malloc(sizeof(int) * n); PH2 = malloc(sizeof(int) * n); EL = malloc(sizeof(int) * n); inv = malloc(sizeof(int) * n);
        for (int h1 = 0; h1 < nh1; h1++) for (int h2 = 0; h2 < nh2; h2++) for (int l = 0; l < n3; l++) {
            int e = (h1 * nh2 + h2) * n3 + l; PH1[e] = h1; PH2[e] = h2; EL[e] = l;
            inv[e] = (iv1[h1] * nh2 + iv2[h2]) * n3 + (n3 - l) % n3; }
        ngen = 0;
        if (pm1 > 1) gens[ngen++] = (pk1 * nh2) * n3;      /* x1 = (1,0) of factor 1 */
        if (pk1 > 1) gens[ngen++] = (1 * nh2) * n3;        /* y1 = (0,1) of factor 1 */
        if (pm2 > 1) gens[ngen++] = pk2 * n3;              /* x2 */
        if (pk2 > 1) gens[ngen++] = 1 * n3;               /* y2 */
        if (n3 > 1) gens[ngen++] = 1;                     /* z */
    } else { fprintf(stderr, "unknown group kind %s\\n", argv[1]); exit(2); }""")
# family_prod + fac_auts before family()
fam = r'''static int *fac_auts(int m, int k, int r, int *cnt) {   /* candidate automorphisms of C_m : C_k: pairs (image of x, image of y) as factor indices */
    int cap = 1 << 16, nc = 0; int *out = malloc(sizeof(int) * 2 * cap);
    int g1 = gcd((r - 1 + m) % m, m);                       /* b only matters mod gcd(r-1, m) up to Inn */
    int bmax = (m > 1 && k > 1) ? g1 : 1;
    for (int a = 0; a < m; a++) {
        if (m > 1 && gcd(a, m) != 1) continue;
        if (m == 1 && a) continue;
        int a2 = (int)((long long)a * a % m), ok = (m == 1);
        for (int j = 0; j < k && !ok; j++) if (ipow(r, j, m) == a2 % m) ok = 1;   /* a^2 in <r> */
        if (!ok) continue;
        for (int c = 0; c < (k > 1 ? k : 1); c++) {
            if (k > 1 && (gcd(c, k) != 1 || (c * c) % k != 1 % k || ipow(r, c, m) != r % m)) continue;
            for (int b = 0; b < bmax; b++) {
                if (nc >= cap) break;
                out[2 * nc] = a * k; out[2 * nc + 1] = (b % m) * k + c; nc++; } } }
    *cnt = nc; return out;
}
static void family_prod(void) {        /* candidates: (aut of factor 1) x (aut of factor 2) x (z -> z^w); make_aut checks them in G */
    int c1, c2; int *L1 = fac_auts(pm1, pk1, pr1, &c1), *L2 = fac_auts(pm2, pk2, pr2, &c2);
    int zl[64], nz = 0;
    if (n3 > 1) { for (int w = 1; w < n3 && nz < 64; w++) if (gcd(w, n3) == 1 && (w * w) % n3 == 1 % n3) zl[nz++] = w; }
    else zl[nz++] = 0;
    nouter = 0;
    for (int i1 = 0; i1 < c1; i1++) for (int i2 = 0; i2 < c2; i2++) for (int zi = 0; zi < nz; zi++) {
        int img[NG], q = 0;
        if (pm1 > 1) img[q++] = (L1[2 * i1] * nh2) * n3;
        if (pk1 > 1) img[q++] = (L1[2 * i1 + 1] * nh2) * n3;
        if (pm2 > 1) img[q++] = L2[2 * i2] * n3;
        if (pk2 > 1) img[q++] = L2[2 * i2 + 1] * n3;
        if (n3 > 1) img[q++] = zl[zi];
        char d[96]; snprintf(d, 96, "F1 x->(%d) y->(%d)  F2 x->(%d) y->(%d)  z->%d", L1[2 * i1], L1[2 * i1 + 1], L2[2 * i2], L2[2 * i2 + 1], zl[zi]);
        add_cand(img, d); }
    free(L1); free(L2);
}
static void family(void) {'''
rep("static void family(void) {", fam)
rep("    if (hkind == 0) {\n        int g1 = gcd(r_ - 1 + m_, m_);",
    "    if (hkind == 4) { family_prod(); return; }\n    if (hkind == 0) {\n        int g1 = gcd(r_ - 1 + m_, m_);")
rep("    if (hkind == 3) { free(perm); free(tmp); return; }", "    if (hkind == 3 || hkind == 4) { free(perm); free(tmp); return; }")
rep("    else printf(\"GROUP %s p %d n3 %d n %d K %d\\n\", argv[1], p_, n3, n, K);",
    "    else if (hkind == 4) printf(\"GROUP prod (%d:%d r %d) x (%d:%d r %d) x C%d n %d K %d\\n\", pm1, pk1, pr1, pm2, pk2, pr2, n3, n, K);\n    else printf(\"GROUP %s p %d n3 %d n %d K %d\\n\", argv[1], p_, n3, n, K);")
open('/home/user/degree-diameter/research/squads/sd5c-r1/c8/fsd_c8.c','w').write(src)
print("patched ok")
