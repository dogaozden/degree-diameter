p = '/home/user/degree-diameter/research/squads/d10D7-r4/c6/ls6.c'
src = open(p).read()
def rep(old, new, count=1):
    global src
    assert src.count(old) == count, ("count mismatch", src.count(old), old[:60])
    src = src.replace(old, new)
rep("static int isline;", "static int isline;\nstatic unsigned char *allowed;")
rep("    if (argc < 7) for (int i = 0; i < N; i++) if (cnt[perm[i]] == 0) addv(perm[i]);",
    "    int use_start = (argc >= 7 && strcmp(argv[6], \"-\") != 0);\n    if (!use_start) for (int i = 0; i < N; i++) if (allowed[perm[i]] && cnt[perm[i]] == 0) addv(perm[i]);")
rep("    if (argc >= 7) {\n        FILE *g = fopen(argv[6], \"r\");",
    "    if (use_start) {\n        FILE *g = fopen(argv[6], \"r\");")
rep("if (x >= 0 && x < N && !inS[x] && cnt[x] == 0)", "if (x >= 0 && x < N && allowed[x] && !inS[x] && cnt[x] == 0)")
rep("""        for (int v = 0; v < N; v++) {
            if (inS[v]) continue;
            if (cnt[v] < bc) { bc = cnt[v]; bv = v; nt = 1; }""",
    """        for (int v = 0; v < N; v++) {
            if (inS[v] || !allowed[v]) continue;
            if (cnt[v] < bc) { bc = cnt[v]; bv = v; nt = 1; }""")
rep("            if (inS[v] || tabuIn[v] > it) continue;", "            if (inS[v] || !allowed[v] || tabuIn[v] > it) continue;")
rep("            if (inS[v] || v == u) continue;", "            if (inS[v] || v == u || !allowed[v]) continue;")
# allowed-set argument and allocation: insert right after the state arrays are allocated
rep("    inS = calloc(N, 1); nb = calloc(N, 1);",
    """    inS = calloc(N, 1); nb = calloc(N, 1);
    allowed = malloc(N);
    memset(allowed, 1, N);
    if (argc >= 8 && strcmp(argv[7], "-") != 0) {
        FILE *g = fopen(argv[7], "r"); int x, na = 0;
        if (!g) { perror(argv[7]); return 2; }
        memset(allowed, 0, N);
        while (fscanf(g, "%d", &x) == 1) if (x >= 0 && x < N) { allowed[x] = 1; na++; }
        fclose(g);
        fprintf(stderr, "allowed set: %d vertices\\n", na);
    }""")
open(p, 'w').write(src)
print("patched allowed-set option")
