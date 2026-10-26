"""Screen (base, group) pairs: 30000 random voltage assignments each with flift eval (cost = min over sample)."""
import subprocess, sys, os
T = "/home/user/degree-diameter/research/squads/b48/tools"
D = "/home/user/degree-diameter/research/squads/b48/r5/k10"
os.chdir(D)
groups = []
for line in open("groups_k10.txt"):
    N, spec, cnt = line.rstrip("\n").split("\t")
    if spec.startswith("meta "):
        m, k, r = spec.split()[1:]
        groups.append((int(N), spec, f"meta:{m}:{k}:{r}"))
groups.append((96, "sl2 3 x cyc 4", f"{D}/sl2_3_c4.bin"))
groups.append((96, "perm 4 1,0,2,3 ; 1,2,3,0 x cyc 4", f"{D}/s4_c4.bin"))
bases = sys.argv[1].split(",")
SAMP = int(sys.argv[2]) if len(sys.argv) > 2 else 30000
out = open("screen.tsv", "w")
for base in bases:
    for N, spec, g in groups:
        gen = subprocess.run(["python3", "gen.py", f"{base}.txt", spec if spec.startswith("meta") else spec, "random", str(SAMP), "7"],
                             capture_output=True, text=True, timeout=120)
        if gen.returncode:
            out.write(f"{base}\t{N}\t{spec}\tGENFAIL {gen.stderr[-200:]}\n"); continue
        r = subprocess.run([f"{T}/flift", f"{base}.txt", g, "3", "9", "eval"], input=gen.stdout, capture_output=True, text=True,
                           env={**os.environ, "LIMIT": "100000", "ONLYLOW": "1", "THREADS": "1"}, timeout=120)
        mn = r.stderr.strip()
        out.write(f"{base}\t{N}\t{spec}\t{mn}\n"); out.flush()
