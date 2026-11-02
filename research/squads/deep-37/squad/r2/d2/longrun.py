"""longrun.py TL FILE... : exhaustive orbdfs169 runs with a long timeout on the listed G-set files (those that timed out
in the quick pass). Appends the same tab-separated lines as run169.py to runs.tsv (status, nodes, sols, secs, far, file)."""
import sys, os, re, subprocess, time
BASE = "/home/user/degree-diameter/research/squads/deep-37"
D2 = BASE + "/squad/r2/d2"
TL = float(sys.argv[1])
for f in sys.argv[2:]:
    deg2 = open(f[:-4] + ".deg2").read().strip()
    env = dict(os.environ, DEG2=deg2, MAXSOL="20", SOLPREFIX=f[:-4] + "_sol")
    ts = time.time()
    try:
        out = subprocess.run([D2 + "/orbdfs169", f, "7"], capture_output=True, text=True, timeout=TL, env=env).stdout
        m = re.search(r"DONE nodes=(\d+) sols=(\d+)(.*)", out)
        if m:
            nodes, sols, tail = m.group(1), m.group(2), m.group(3)
            st = "EXCL" if "EXCLUDED" in tail else "DONE"
        else:
            nodes, sols, st = "-", str(out.count("SOL ")), "ERR"
    except subprocess.TimeoutExpired:
        nodes, sols, st = "-", "-", "TIMEOUT%d" % TL
    secs = time.time() - ts
    far = "-"
    if st == "DONE" and sols != "0":
        fars = []
        for i in range(1, int(sols) + 1):
            r = subprocess.run([BASE + "/bin/score37", f[:-4] + "_sol_%d.edges" % i], capture_output=True, text=True)
            mm = re.search(r"far=(\d+)", r.stdout); fars.append(mm.group(1) if mm else "?")
        far = ",".join(fars)
    with open(D2 + "/runs.tsv", "a") as fh:
        fh.write("\t".join([f, st, nodes, sols, "%.1f" % secs, far, "long"]) + "\n")
    print(f, st, nodes, sols, "%.1f" % secs, flush=True)
