import sys
sys.path.insert(0, "/home/user/degree-diameter/research/squads/raise10/tools")
import groups
for line in open("/home/user/degree-diameter/research/squads/raise10/r4/h11/specs2.txt"):
    name, spec, order = line.strip().split("|")
    T = groups.table(spec)
    N = len(T)
    print(name, "N=", N, "expected", order, "OK" if N == int(order) else "MISMATCH", flush=True)
    groups.write_bin(T, "/home/user/degree-diameter/research/squads/raise10/r4/h11/%s.bin" % name)
