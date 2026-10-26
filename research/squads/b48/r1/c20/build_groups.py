# Writes lift-format .bin tables for the non-metacyclic groups of order 365..420 used in the screen.
import sys, os, time
sys.path.insert(0, "/home/user/degree-diameter/research/squads/b48/tools")
import groups
SPECS = {
    "sl2_3x16": "sl2 3 x cyc 16",
    "s4x16": "perm 4 1,0,2,3 ; 1,2,3,0 x cyc 16",
    "a4x32": "perm 4 1,2,0,3 ; 1,0,3,2 x cyc 32",
    "agl1_5x20": "agl1 5 x cyc 20",
    "heis3x14": "heis 3 x cyc 14",
    "a5x7": "psl2 5 x cyc 7",
    "semi7_8": "semi 7 8 0 6 1 0",
    "sl2_3x17": "sl2 3 x cyc 17",
    "s4x17": "perm 4 1,0,2,3 ; 1,2,3,0 x cyc 17",
}
OUT = "/home/user/degree-diameter/research/squads/b48/r1/c20/groups"
for name, spec in SPECS.items():
    t = time.time()
    T = groups.table(spec)
    groups.check(T)
    groups.write_bin(T, os.path.join(OUT, name + ".bin"))
    print(name, len(T), "%.1fs" % (time.time() - t), flush=True)
