#!/usr/bin/env python3
"""Mean BFS ball sizes (cumulative, alternating sides) of random beta-invariant S, by twisted 4-/8-cycle class,
against random S.  Usage: levels_by_class.py RANDORB.jsonl RANDSAMPLE.jsonl"""
import json, sys, gzip
import numpy as np
def load(p):
    rows = [json.loads(l) for l in (gzip.open(p, 'rt') if p.endswith('.gz') else open(p))]
    return [r for r in rows if "header" not in r]
sym, rnd = load(sys.argv[1]), load(sys.argv[2])
N = max(max(r["levels"]) for r in rnd)
def lv(rows): return np.array([r["levels"] for r in rows], float)
def ok(rows): return [r for r in rows if r["cost"] < N / 2]
sym, rnd = ok(sym), ok(rnd)
Lr = lv(rnd)
iv4 = np.array([r["census"]["2"]["involutive"] for r in rnd]); iv8 = np.array([r["census"]["4"]["involutive"] for r in rnd])
print("random S (all generating):        ", np.round(Lr.mean(0)).astype(int), "median cost", np.median([r["cost"] for r in rnd]))
m = (iv4 == 0) & (iv8 == 0)
print("random S, no involutive 4/8-cycles:", np.round(Lr[m].mean(0)).astype(int), "median cost", np.median([r["cost"] for r, k in zip(rnd, m) if k]), "n", m.sum())
t4 = np.array([r["census"]["2"]["twisted"] for r in sym]) // 8; t8 = np.rint(np.array([r["census"]["4"]["twisted"] for r in sym]) / 16)
i4 = np.array([r["census"]["2"]["involutive"] for r in sym]); i8 = np.array([r["census"]["4"]["involutive"] for r in sym])
Ls = lv(sym)
for a in (0, 1):
    for b in range(0, 7):
        mm = (t4 == a) & (t8 == b) & (i4 == 0) & (i8 == 0)
        if mm.sum() >= 10:
            print(f"sym n4={a} n8={b} (no involutive 4/8):", np.round(Ls[mm].mean(0)).astype(int), "median cost", np.median([r["cost"] for r, k in zip(sym, mm) if k]), "n", mm.sum())
