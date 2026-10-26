import sys
sys.path.insert(0, "/home/user/degree-diameter/research/squads/b48/tools")
import groups, numpy as np
specs = [l.split(":",1)[1].strip() for l in open("/home/user/degree-diameter/research/squads/b48/r1/c45/specs.txt")]
for i, s in enumerate(specs, 1):
    T = groups.table(s)
    N = len(T)
    ok = "bad"
    try:
        groups.check(T); ok = "ok"
    except AssertionError as e:
        ok = "FAIL " + str(e)
    path = f"/home/user/degree-diameter/research/squads/b48/r1/c45/g{i}.bin"
    groups.write_bin(T, path)
    print(i, s, "N=", N, "2N=", 2*N, ok, flush=True)
