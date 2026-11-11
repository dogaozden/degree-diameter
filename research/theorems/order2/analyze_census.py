#!/usr/bin/env python3
"""Cost of random beta-invariant S against their twisted-relator census (output of twist.py randorb/randsample).
Usage: analyze_census.py FILE.jsonl [FILE2.jsonl ...]"""
import json, sys, gzip, math
import numpy as np


def load(path):
    hdr, rows = None, []
    for ln in (gzip.open(path, 'rt') if path.endswith('.gz') else open(path)):
        r = json.loads(ln)
        if "header" in r:
            hdr = r["header"]
        else:
            rows.append(r)
    return hdr, rows


def q(a, p):
    return float(np.percentile(a, p)) if len(a) else float("nan")


for path in sys.argv[1:]:
    hdr, rows = load(path)
    N = hdr["N"] if hdr else None
    cost = np.array([r["cost"] for r in rows])
    if N is None:
        N = max(r["levels"][-1] for r in rows)
    Ls = sorted(int(k) for k in rows[0]["census"])
    tw = {L: np.array([r["census"][str(L)]["twisted"] for r in rows]) for L in Ls}
    iv = {L: np.array([r["census"][str(L)]["involutive"] for r in rows]) for L in Ls}
    gen = cost < N / 2          # S generating (not stuck in a subgroup)
    print(f"== {path}: {len(rows)} samples, header {json.dumps(hdr) if hdr else '(random S)'}")
    print(f"   degenerate (cost >= N/2): {np.sum(~gen)}")
    c = cost[gen]
    print(f"   cost over generating S: min {c.min()} p1 {q(c,1):.0f} p10 {q(c,10):.0f} median {q(c,50):.0f} mean {c.mean():.1f}")
    for L in Ls:
        t = tw[L][gen]; v = iv[L][gen]
        print(f"   length {L}: twisted half-words mean {t.mean():.2f} (relators {t.mean()/(4*L):.3f}), P(0) {np.mean(t==0):.3f};"
              f" involutive mean {v.mean():.2f}, P(0) {np.mean(v==0):.3f}")
    if hdr:
        L2 = Ls[0]; L4 = Ls[1] if len(Ls) > 1 else None
        # cost by number of twisted relators of length 4 (L=2) and 8 (L=4)
        r4 = np.rint(tw[2][gen] / 8).astype(int)
        r8 = np.rint(tw[4][gen] / 16).astype(int) if L4 else np.zeros_like(r4)
        print("   cost by twisted 4-cycles (n4) and 8-cycles (n8): n4 n8 count min p10 median mean")
        for a in range(0, r4.max() + 1):
            for b in range(0, min(r8.max(), 8) + 1):
                m = (r4 == a) & (r8 == b)
                if m.sum() >= 5:
                    cc = c[m]
                    print(f"     {a} {b} {m.sum():5d} {cc.min():6d} {q(cc,10):7.0f} {q(cc,50):7.0f} {cc.mean():8.1f}")
        # log-linear fit of median cost on n4, n8, n12
        X = np.column_stack([np.ones(gen.sum()), r4, r8] + ([tw[6][gen] / 24.0] if 6 in tw else []))
        y = np.log(np.maximum(c, 1))
        beta, *_ = np.linalg.lstsq(X, y, rcond=None)
        print("   ln(cost) ~ " + " + ".join(f"{b:.3f}*{n}" for b, n in zip(beta, ["1", "n4", "n8", "n12"])))
    else:
        r4 = np.rint(iv[2][gen] / 8).astype(int)
        r8 = np.rint(iv[4][gen] / 16).astype(int)
        print("   cost by involutive 4-cycles (n4) and 8-cycles (n8): n4 n8 count min p10 median mean")
        for a in range(0, r4.max() + 1):
            for b in range(0, min(r8.max(), 8) + 1):
                m = (r4 == a) & (r8 == b)
                if m.sum() >= 5:
                    cc = c[m]
                    print(f"     {a} {b} {m.sum():5d} {cc.min():6d} {q(cc,10):7.0f} {q(cc,50):7.0f} {cc.mean():8.1f}")
    print()
