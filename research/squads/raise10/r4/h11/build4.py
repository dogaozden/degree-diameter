import sys
sys.path.insert(0, "/home/user/degree-diameter/research/squads/raise10/tools")
import groups
specs = [
    ("F42xZ10", "agl1 7 x cyc 10", 420),
    ("F42xD10", "agl1 7 x dih 5", 420),
    ("GD9xSL23", "perm 9 1,2,0,4,5,3,7,8,6 ; 3,4,5,6,7,8,0,1,2 ; 0,2,1,3,5,4,6,8,7 x sl2 3", 432),
    ("SL23xZ2xZ3xZ3", "sl2 3 x cyc 2 x cyc 3 x cyc 3", 432),
    ("F20xF21xZ? ", "agl1 5 x cyc 21", 420),
]
for name, spec, o in specs:
    T = groups.table(spec)
    N = len(T)
    print(name, "N=", N, "expected", o, "OK" if N == o else "MISMATCH", flush=True)
    groups.write_bin(T, "/home/user/degree-diameter/research/squads/raise10/r4/h11/%s.bin" % name.replace(" ", "").replace("?", ""))
