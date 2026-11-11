# Median wall time (20 runs, process start included) of tools/apsp and tools/score48 on three regular bipartite graphs.
import subprocess, time, statistics, os
H = "/home/user/degree-diameter/research/squads/handsoff-49"
T = f"{H}/tools"; W = f"{H}/w26"
cases = [("4-reg n=4970 (valid4970)", f"{H}/seeds/valid4970.edges", 4, 9),
         ("3-reg n=170 (random)", f"{W}/rand3_170.edges", 3, 7),
         ("6-reg n=686 (random)", f"{W}/rand6_686.edges", 6, 5)]
for tool in ["apsp", "score48"]:
    for name, path, d, D in cases:
        ts, last = [], ""
        load0 = os.getloadavg()[0]
        for _ in range(20):
            t0 = time.perf_counter()
            p = subprocess.run(["nice", "-n", "10", f"{T}/{tool}", path, str(d), str(D)], capture_output=True, text=True, timeout=60)
            ts.append(time.perf_counter() - t0)
            last = (p.stdout.strip().splitlines() or [""])[-1]
        print(f"{tool}\t{name}\tmedian_ms={1e3*statistics.median(ts):.2f}\tmin_ms={1e3*min(ts):.2f}\tmax_ms={1e3*max(ts):.2f}\tload1_before={load0:.2f}\tlast_line={last}", flush=True)
