# Builds the group tables used by card c21 (order 274..300, non-dihedral except the dihedral controls).
import sys
sys.path.insert(0, "/home/user/degree-diameter/research/squads/b48/tools")
import groups
OUT = "/home/user/degree-diameter/research/squads/b48/r1/c21/groups/"
specs = {
    "S4xZ12": "perm 4 1,0,2,3 ; 1,2,3,0 x cyc 12",
    "SL23xZ12": "sl2 3 x cyc 12",
    "A4xZ24": "perm 4 1,2,0,3 ; 1,0,3,2 x cyc 24",
    "Z7sqxZ6": "semi 7 6 3 0 0 3",
    "A5xZ5": "perm 5 1,2,0,3,4 ; 1,2,3,4,0 x cyc 5",
    "meta72_4_17": "meta 72 4 17",
    "dih145": "meta 145 2 144",
    "dih137": "meta 137 2 136",
    "meta23_12_22": "meta 23 12 22",
    "dih141": "meta 141 2 140",
    "A4xZ23": "perm 4 1,2,0,3 ; 1,0,3,2 x cyc 23",
    "agl1_5xZ14": "agl1 5 x cyc 14",
    "dih140": "meta 140 2 139",
    "agl1_7xZ7": "agl1 7 x cyc 7",
}
for name, spec in specs.items():
    groups.write_bin(groups.table(spec), OUT + name + ".bin")
