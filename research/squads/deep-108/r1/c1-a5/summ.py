# usage: summ.py NAME [NAME...]  -- E_s from info_NAME.txt census, sample stats from samp_NAME.tsv (or pair0.tsv with NAME=pair0)
import sys, math, re, statistics
N = 615960; lam = 5380840 / N
for name in sys.argv[1:]:
    cen = {}
    try:
        for tok in re.findall(r"c(\d+):(\d+)", open(f"info_{name}.txt").read()):
            cen[int(tok[0])] = int(tok[1])
    except FileNotFoundError:
        pass
    Es = sum(cnt * math.exp(-lam * s / 10) for s, cnt in cen.items() if s != 10)
    fn = "pair0.tsv" if name == "pair0" else f"samp_{name}.tsv"
    rows = [l.split() for l in open(fn) if l.startswith("M ")]
    C = []; conn = 0; minc = None
    for r in rows:
        uBA, uAA, uBB = int(r[3]), int(r[4]), int(r[5])
        if uBA + uAA <= 300:
            conn += 1; c = uBA + uAA + uBB
            minc = c if minc is None else min(minc, c)
        else:
            c = uBA + uAA   # lower bound (B-root not computed)
        C.append(c)
    C.sort()
    med = statistics.median(C) if C else None
    print(f"{name}: census {cen} E_s={Es:.3f} n={len(rows)} connected={conn} minC(conn)={minc} median(proxy)={med} p10={C[len(C)//10] if C else None}")
