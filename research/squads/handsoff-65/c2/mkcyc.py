import sys
# cyclic group C_m table, tabu/vl format: m then m rows (element 0 = identity)
m = int(sys.argv[1]); out = sys.argv[2]
with open(out, "w") as f:
    f.write(f"{m}\n")
    for g in range(m):
        f.write(" ".join(str((g + h) % m) for h in range(m)) + "\n")
