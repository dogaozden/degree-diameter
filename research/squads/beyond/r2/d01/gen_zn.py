import sys
n = int(sys.argv[1]); out = sys.argv[2]
with open(out, 'w') as f:
    f.write(f"{n}\n")
    for a in range(n):
        f.write(" ".join(str((a + b) % n) for b in range(n)) + "\n")
