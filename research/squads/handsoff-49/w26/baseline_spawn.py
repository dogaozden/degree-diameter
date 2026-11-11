# Process-start baseline: median wall time of apsp on a 4-vertex graph (no real work), 20 runs.
import subprocess, time, statistics
T = "/home/user/degree-diameter/research/squads/handsoff-49/tools"
ts = []
for _ in range(20):
    t0 = time.perf_counter()
    subprocess.run(["nice", "-n", "10", f"{T}/apsp", "tiny4cycle.edges", "2", "2"], capture_output=True, text=True, timeout=60)
    ts.append(time.perf_counter() - t0)
print(f"apsp tiny4cycle (process start only) median_ms={1e3*statistics.median(ts):.2f} min_ms={1e3*min(ts):.2f}")
