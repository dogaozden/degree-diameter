p = '/home/user/degree-diameter/research/squads/d10D7-r4/c6/ls6.c'
src = open(p).read()
old = """    F = recountF();
    fprintf(stderr, "greedy start size %d\\n", k);"""
new = """    /* optional start set (plain id file, argv[6]): added first where conflict free */
    if (argc >= 7) {
        FILE *g = fopen(argv[6], "r"); int x, added = 0;
        if (g) { while (fscanf(g, "%d", &x) == 1) { if (x >= 0 && x < N && !inS[x] && cnt[x] == 0) { addv(x); added++; } } fclose(g); }
        fprintf(stderr, "start file: added %d of the ids\\n", added);
    }
    F = recountF();
    fprintf(stderr, "greedy start size %d\\n", k);"""
assert src.count(old) == 1, "pattern not found"
src = src.replace(old, new)
src = src.replace('if (argc < 6) { fprintf(stderr, "usage: ls6 HEXBIN points|lines SECONDS SEED OUTPREFIX\\n"); return 2; }',
                  'if (argc < 6) { fprintf(stderr, "usage: ls6 HEXBIN points|lines SECONDS SEED OUTPREFIX [STARTFILE]\\n"); return 2; }')
open(p, 'w').write(src)
print("patched start option")
