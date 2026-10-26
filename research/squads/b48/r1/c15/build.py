import sys
sys.path.insert(0, "/home/user/degree-diameter/research/squads/b48/tools")
import groups, numpy as np
specs = {
 "A": "dih 3 x dih 92",
 "B": "dih 5 x dih 55",
 "C": "sl2 3 x dih 23",
 "D": "perm 4 1,2,0,3 ; 0,2,3,1 x dih 46",
 "E": "dih 3 x dih 3 x cyc 31",
 "F": "meta 7 3 2 x dih 27",
 "G": "meta 5 4 2 x dih 28",
 "H": "dih 4 x dih 69",
 "I": "dih 7 x dih 40",
 "J": "sl2 3 x dih 24",
}
for k, s in specs.items():
    T = groups.table(s)
    N = len(T)
    groups.check(T) if N <= 1200 else None
    groups.write_bin(T, f"/home/user/degree-diameter/research/squads/b48/r1/c15/G{k}.bin")
    print(k, N, s, flush=True)
