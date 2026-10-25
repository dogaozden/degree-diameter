"""c2 helper: write the GAP multiplication table of SmallGroup(n, i) to a stable path (for lanneal).
Usage (cwd = smallfam, SCRATCH set): python3 prep_table.py n i OUT"""
import os, shutil, sys
sys.path.insert(0, '/home/user/degree-diameter/research/theorems/smallfam')
from screen import export_table  # noqa: E402
n, i, out = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3]
struct, tab = export_table(n, i)
shutil.move(tab, out)
print(struct, out)
