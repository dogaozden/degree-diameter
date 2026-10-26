import sys, time
sys.path.insert(0, "/home/user/degree-diameter/research/squads/b48/r1/c08")
from alevel import run
m, k, r = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
lo, hi = int(sys.argv[4]), int(sys.argv[5])
rows = open(sys.argv[6]).read().split("\n")
rows = [x for x in rows if x.strip()]
for line in rows[lo:hi]:
    stratum, js = line.split()
    J = [0] + [int(x) for x in js.split(",")]
    best, nev, mn, ninv, err = run(m, k, r, J)
    cost = best[0] if best else None
    print(f"{stratum} J={J} best={cost} at={best[1] if best else None} invalid={ninv}", flush=True)
