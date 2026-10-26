# Screen (base, group) pairs for D=11, d=3: lift annealing with a short budget; logs one RESULT line per run.
import subprocess, sys, os, re, glob
SECS = sys.argv[1]; OUT = sys.argv[2]
groups = ["sl2 3 x cyc 12", "sl2 3 x cyc 8", "sl2 3 x cyc 9", "sl2 3 x cyc 6", "agl1 7 x cyc 7", "agl1 13",
          "dih 75", "dih 90", "dih 70", "agl1 11 x cyc 2", "psl2 7", "sl2 5 x cyc 2", "agl1 19", "sl2 3 x cyc 13",
          "dih 100", "agl1 11 x cyc 3", "heis 5 x cyc 3"]
bases = {4: ["bases/bip4_0.txt"], 6: ["bases/bip6_0.txt", "bases/bip6_1.txt", "bases/bip6_2.txt"],
         8: sorted(glob.glob("bases/bip8_*.txt"))}
def gfile(spec):
    f = "groups/" + spec.replace(" ", "_") + ".bin"
    if not os.path.exists(f):
        subprocess.run(["python3", "groups.py", spec, f], check=True, capture_output=True)
    return f
log = open(OUT, "a")
for spec in groups:
    g = gfile(spec)
    N = int(open(g, "rb").read(4) and __import__("struct").unpack("<i", open(g, "rb").read(4))[0])
    for b, bl in bases.items():
        if b * N <= 1008 or b * N > 1800: continue
        for base in bl:
            tag = os.path.basename(base)[:-4] + "_" + spec.replace(" ", "")
            r = subprocess.run(["./lift", base, g, "3", "11", SECS, "1", "8", "runs/s_" + tag],
                               capture_output=True, text=True, timeout=300)
            line = [l for l in r.stdout.splitlines() if l.startswith("RESULT")]
            log.write(f"{spec} | {base} | " + (line[0] if line else r.stderr[-200:]) + "\n"); log.flush()
