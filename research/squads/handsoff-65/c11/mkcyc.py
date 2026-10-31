import sys
m = int(sys.argv[1]); out = sys.argv[2]
with open(out, 'w') as f:
    f.write("%d\n" % m)
    for g in range(m): f.write(" ".join(str((g + h) % m) for h in range(m)) + "\n")
