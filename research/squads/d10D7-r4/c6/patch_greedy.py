p = '/home/user/degree-diameter/research/squads/d10D7-r4/c6/ls6.c'
src = open(p).read()
old = "    for (int i = 0; i < N; i++) if (cnt[perm[i]] == 0) addv(perm[i]);"
new = "    if (argc < 7) for (int i = 0; i < N; i++) if (cnt[perm[i]] == 0) addv(perm[i]);"
assert src.count(old) == 1, "pattern not found"
open(p, 'w').write(src.replace(old, new))
print("greedy now skipped when a start file is given")
