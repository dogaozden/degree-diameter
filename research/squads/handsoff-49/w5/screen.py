"""Screen (base, group) pairs with flift. Usage: python3 screen.py SECS OUTTSV BASE[,BASE..] GROUP[,GROUP..] [SEED]
GROUP is meta:m:k:r (validated here) or a path to a .bin table. Appends 'base group n best secs' lines to OUTTSV."""
import sys, subprocess, re, os
HERE = os.path.dirname(os.path.abspath(__file__))
secs, outp = float(sys.argv[1]), sys.argv[2]
bases = sys.argv[3].split(","); groups = sys.argv[4].split(",")
seed = sys.argv[5] if len(sys.argv) > 5 else "1"
def valid_meta(spec):
    m, k, r = map(int, spec.split(":")[1:])
    return pow(r, k, m) == 1 % m
for g in groups:
    if g.startswith("meta:") and not valid_meta(g):
        print("INVALID GROUP", g); continue
    for b in bases:
        try:
            p = subprocess.run(["nice", "-n", "10", os.path.join(HERE, "..", "tools", "flift"), b, g, "4", "9", str(secs), seed],
                               capture_output=True, text=True, timeout=secs + 60)
            line = [l for l in p.stdout.splitlines() if l.startswith("RESULT")]
            m = re.search(r"best=(\d+)", line[0]) if line else None
            nn = re.search(r"n=(\d+)", line[0]).group(1) if line else "?"
            best = m.group(1) if m else "ERR"
        except subprocess.TimeoutExpired:
            best, nn = "TIMEOUT", "?"
        with open(outp, "a") as f:
            f.write(f"{os.path.basename(b)}\t{g}\t{nn}\t{best}\t{secs}\n")
        print(f"{os.path.basename(b)} {g} n={nn} best={best}", flush=True)
