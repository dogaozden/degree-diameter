import sys, time
sys.path.insert(0, "/home/user/degree-diameter/research/squads/b48/r1/c08")
from alevel import run
for js in sys.argv[1:]:
    J = [int(x) for x in js.split(",")]
    t0=time.time(); best, nev, mn, ninv, err = run(110, 10, 9, J)
    print(f"m=110 k=10 r=9 J={J} evals={nev} best={best[0] if best else None} at={best[1] if best else None} invalid={ninv} t={time.time()-t0:.1f}", flush=True)
