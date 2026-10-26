import sys; sys.path.insert(0, "/home/user/degree-diameter/research/squads/b48/tools")
import groups as G
a=(1, 5, 7, 3, 6, 2, 4, 8, 0); b=(1, 5, 0, 3, 7, 4, 2, 8, 6)
T = G.t_perm(9, [list(a), list(b)]); print(len(T)); G.write_bin(T, "/home/user/degree-diameter/research/squads/b48/r1/c17/tab/rand9_1152.bin")
