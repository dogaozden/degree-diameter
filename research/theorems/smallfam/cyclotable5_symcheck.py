"""Check of the symmetry reduction in cyclotable5.py: the unreduced cyclobound.bound (units only) must give the same
B(k, o) as the reduced table. Usage: python3 cyclotable5_symcheck.py D k:o [k:o ...]"""
import sys
import cyclobound
cyclobound.FIBER = True
D = int(sys.argv[1])
for ko in sys.argv[2:]:
    k, o = map(int, ko.split(':'))
    B, j = cyclobound.bound(5, D, k, o)
    print(f'Delta=5 D={D} k={k} o={o}: unreduced B = {B} at {j} ({len(list(cyclobound.admissible_js(5, k, o)))} patterns)',
          flush=True)
