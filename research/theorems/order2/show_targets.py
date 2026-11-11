#!/usr/bin/env python3
"""Print the binned miss rates of targets.py JSON outputs.  Usage: show_targets.py FILE.json ..."""
import json, sys
for p in sys.argv[1:]:
    r = json.load(open(p))
    print(f"== {p}: {r['group']} N={r['N']} d={r['d']} D={r['D']} m={r['m']} f={r['f']} random={r['random']} "
          f"frob={r['frob']} r={r['r']} sizes={r['class_sizes']} used={r['samples_used']} median cost={r['median_cost']}")
    print("   bin  samples  other      sqrt(other)  Fix        Anti       Anti/other  Anti/sqrt(other)  Fix/sqrt(other)")
    for i, b in enumerate(r["bins_by_generic_rate"]):
        f = lambda x: f"{x:.5f}" if isinstance(x, float) else str(x)
        g = lambda x: f"{x:.2f}" if isinstance(x, float) else str(x)
        print(f"   {i}    {b['samples']:5d}    {f(b['other'])}    {f(b['sqrt_other'])}      {f(b['Fix'])}    {f(b['Anti'])}    "
              f"{g(b['Anti_over_other'])}        {g(b['Anti_over_sqrt_other'])}              {g(b['Fix_over_sqrt_other'])}")
