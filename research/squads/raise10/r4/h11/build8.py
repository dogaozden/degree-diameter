import sys
sys.path.insert(0, "/home/user/degree-diameter/research/squads/raise10/tools")
import groups
specs = [
    ("S3cubedxZ2", "dih 3 x dih 3 x dih 3 x cyc 2", 432),
    ("S3xS3xD12", "dih 3 x dih 3 x dih 6", 432),
    ("S3xS3xZ12", "dih 3 x dih 3 x cyc 12", 432),
    ("S3xS3xZ2xZ6", "dih 3 x dih 3 x cyc 2 x cyc 6", 432),
    ("D12xS3xZ6", "dih 6 x dih 3 x cyc 6", 432),
]
for name, spec, o in specs:
    T = groups.table(spec)
    N = len(T)
    print(name, "N=", N, "expected", o, "OK" if N == o else "MISMATCH", flush=True)
    if N == o:
        groups.write_bin(T, "/home/user/degree-diameter/research/squads/raise10/r4/h11/%s.bin" % name)
