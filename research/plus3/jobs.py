"""Print one job line per symmetry case for sat_ext.py: --sym A plus --conc r, r = 2..q+1.
Usage: python jobs.py q kP kL E ADD [extra args...]"""
import sys
q, kP, kL, E, ADD = sys.argv[1:6]
extra = ' '.join(sys.argv[6:])
print(f'{q} {kP} {kL} {E} {ADD} --sym A {extra}'.strip())
for r in range(2, int(q) + 2):
    print(f'{q} {kP} {kL} {E} {ADD} --conc {r} {extra}'.strip())
