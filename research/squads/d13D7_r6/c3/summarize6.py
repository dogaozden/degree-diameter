#!/usr/bin/env python3
"""Card c3 (squad round 6): table of the groups run by shapes6.py (reads runlog.jsonl)."""
import json
import os

HERE = os.path.dirname(os.path.abspath(__file__))
rows = []
with open(os.path.join(HERE, 'runlog.jsonl')) as f:
    for line in f:
        line = line.strip()
        if line:
            rows.append(json.loads(line))
print(f'{"shape":<22}{"K":>7}{"norb":>8}{"w":>6}{"opt":>7}{"texact":>8}{"theur":>7}  skipped')
for r in rows:
    if 'norbits' not in r:
        print(f'{r.get("shape", "?"):<22}  -- {r.get("skipped")}')
        continue
    print(f'{r["shape"]:<22}{r["K"]:>7}{r["norbits"]:>8}{r["weight"]:>6}{str(r["optimal"]):>7}'
          f'{str(r.get("texact", "")):>8}{str(r.get("theur", "")):>7}  {r.get("skipped") or ""}')
best = max((r for r in rows if r.get('weight')), key=lambda r: r['weight'], default=None)
print('best:', None if best is None else (best['weight'], best['shape'], best['fp']))
