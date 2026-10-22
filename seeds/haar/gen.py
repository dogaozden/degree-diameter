#!/usr/bin/env python3
"""Stamp out the Haar seed programs: core.py + a per-cell plan.  Run from anywhere:  python3 seeds/haar/gen.py

Each output (seeds/haar/<name>.py) is ONE self-contained program with the evolve interface build(d, D, seed, time_limit),
because Haiku mutates a single file.  Edit PLANS below (near-miss sets, group lists, fallback), then re-run.
"""
import json
from pathlib import Path

HERE = Path(__file__).parent
CORE = (HERE / "core.py").read_text()
NM = json.loads((HERE / "nearmiss.json").read_text())   # produced by the C searches, see nearmiss.json

TEMPLATE = '''

# ======================================================================================== cell: {cell}
# {blurb}
TARGET = ({d}, 5)      # the (d, D) this plan is for; every other case gets a small always-valid graph

# (name, group builder, start set S0 or None, share of the time budget).  S0 = element indices of the group table.
PLAN = [
{plan}
]

# Valid smaller Haar graph, checked at run time; used only when no plan entry reaches cost 0.
FALLBACK = ({fb_builder}, {fb_S})


def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return trivial(d, D)
    return run(d, D, seed, time_limit, PLAN, FALLBACK)
'''

PLANS = {}
exec((HERE / "plans.py").read_text(), {"NM": NM, "PLANS": PLANS})

for name, p in PLANS.items():
    plan = "\n".join(f"    ({n!r}, lambda: {b}, {s0!r}, {w})," for n, b, s0, w in p["plan"])
    text = CORE + TEMPLATE.format(cell=p["cell"], blurb=p["blurb"], d=p["d"], plan=plan,
                                  fb_builder="lambda: " + p["fallback"][0], fb_S=p["fallback"][1])
    (HERE / f"{name}.py").write_text(text)
    print("wrote", HERE / f"{name}.py", len(text.splitlines()), "lines")
