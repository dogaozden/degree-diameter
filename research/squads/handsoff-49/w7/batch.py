"""Screen (group table, involution/order-3 subgroup H) pairs with bicos. Usage: python3 batch.py LOG SA_SECS EXH_LIMIT TABLE...
For each non-central class rep t of order h in {2,3}: H = <t>; for each k-composition of 4: exhaustive if the number of S
is <= EXH_LIMIT, else simulated annealing for SA_SECS seconds. Results appended to LOG (TSV)."""
import subprocess, sys, os, re, time
HERE = os.path.dirname(os.path.abspath(__file__))
BIC = os.path.join(HERE, "bicos")
APSP = os.path.join(HERE, "..", "tools", "apsp")
log, sa_secs, exh_limit = sys.argv[1], float(sys.argv[2]), float(sys.argv[3])
tables = sys.argv[4:]
def run(args, timeout=530):
    try:
        r = subprocess.run(["nice", "-n", "10", BIC] + args, capture_output=True, text=True, timeout=timeout)
        return r.stdout + r.stderr
    except subprocess.TimeoutExpired:
        return "TIMEOUT"
def append(line):
    with open(log, "a") as f:
        f.write(line + "\n")
for tab in tables:
    name = os.path.basename(tab)
    out = run([tab, "classes"], 200)
    reps = []
    for line in out.splitlines():
        m = re.match(r"class rep=(\d+) order=(\d+) size=(\d+) centralizer=(\d+)", line)
        only = os.environ.get("ONLY_H")
        if m and int(m.group(3)) > 1 and (only is None or int(m.group(2)) == int(only)):
            reps.append((int(m.group(1)), int(m.group(2)), int(m.group(3)), int(m.group(4))))
    append(f"# {name}: {len(reps)} non-central class reps (rep order size cent)")
    for rep, order, size, cent in reps:
        info = run([tab, "info", str(rep)], 200)
        mm = re.search(r"N=(\d+) h=(\d+) M=(\d+) n=(\d+)", info)
        if not mm:
            append(f"{name}\t{rep}\tinfo-fail\t{info[:200]}")
            continue
        N, h, M, n = map(int, mm.groups())
        counts = dict(re.findall(r"\{([\d,]+)\}=(\d+)", info))
        if h == 2:
            comps = ["2,2", "1,1,2"]
        elif h == 3:
            comps = ["1,3"]
        else:
            continue
        if n < 4971:
            append(f"{name}\t{rep}\th={h}\tn={n}\tskipped (n < 4971)")
            continue
        for comp in comps:
            cnt = 0
            if comp in counts:
                cnt = int(counts[comp])
            else:
                cnt = None
            # counts printed by bicos use the names {1,1,1,1}, {1,1,2}, {2,2}, {1,3}
            key = comp
            cnt = int(counts.get(key, 0))
            if cnt == 0:
                continue
            if cnt <= exh_limit:
                res = run([tab, "exh", str(rep), comp, str(int(exh_limit)), os.path.join(HERE, "tabs", f"best_{name}_{rep}_{comp.replace(',','')}.edges")])
                mode = "exh"
            else:
                res = run([tab, "sa", str(rep), comp, str(sa_secs), "1", os.path.join(HERE, "tabs", f"best_{name}_{rep}_{comp.replace(',','')}.edges")])
                mode = "sa"
            cm = re.search(r"best C=(\d+)", res)
            sm = re.search(r"best (?:C=\d+ )?S=(.*)", res)
            C = int(cm.group(1)) if cm else -1
            append(f"{name}\t{rep}\th={h}\tn={n}\tcomp={comp}\tcount={cnt}\tmode={mode}\tC={C}\t{(sm.group(1) if sm else res[:120]).strip()}")
    append(f"# done {name}")
