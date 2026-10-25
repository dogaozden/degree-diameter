"""Exhaustive normal-form Haar search at (4,9) for Z101 x|_r Z25 with r of order 25 (= SmallGroup(2525,3)), via
frob_scan.run (hx meta, normal form S = {(0,0), (0,j1), (1,j2), s3}, quotient filter)."""
import os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from frob_scan import actions, run
for r, o in actions(101, 25):
    if o != 25:
        continue
    tested, nsol, best, sols = run(101, 25, r, o, 4, 9, int(sys.argv[1]) if len(sys.argv) > 1 else 2, 20)
    print(f'Z101 x|_{r} Z25 (ord r = {o}, N = 2525): tested={tested} solutions={nsol} best={best}'
          f' (at odd D, best >= N means N + uncovered in the first BFS)', flush=True)
    for s in sols:
        print(s, flush=True)
