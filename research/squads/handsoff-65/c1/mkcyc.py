# usage: mkcyc.py m OUT   -- cyclic group table
import sys
m = int(sys.argv[1])
with open(sys.argv[2], "w") as f:
    f.write("%d\n" % m)
    for g in range(m):
        f.write(" ".join(str((g + h) % m) for h in range(m)) + "\n")
