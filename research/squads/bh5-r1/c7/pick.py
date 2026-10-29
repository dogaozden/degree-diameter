# best-of-N smart deletion: grow.py with seed s, score start cost with ga SECS=0, keep the lowest.
import subprocess, sys, re, shutil
B = "/home/user/degree-diameter/research/beyond-haar-d5"
inp, delta, K, N, out = sys.argv[1], sys.argv[2], sys.argv[3], int(sys.argv[4]), sys.argv[5]
best = None
for s in range(N):
    tmp = f"/home/user/degree-diameter/research/squads/bh5-r1/c7/cand.edges"
    subprocess.run(["python3", f"{B}/src/grow.py", inp, tmp, delta, K, str(1000 + s)], check=True,
                   stdout=subprocess.DEVNULL)
    r = subprocess.run([f"{B}/ga", tmp], env={"D": "5", "DELTA": delta, "SECS": "0", "OUT": tmp + ".o"},
                       capture_output=True, text=True, timeout=120)
    m = re.search(r"RESULT best (\d+)", r.stdout)
    c = int(m.group(1))
    if best is None or c < best[0]:
        best = (c, s)
        shutil.copy(tmp, out)
        print("seed", s, "start cost", c, flush=True)
print("BEST", best, flush=True)
