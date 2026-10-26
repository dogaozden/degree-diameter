"""Build group tables (format of research/squads/b48/tools/groups.py) for e01. Usage: mktab.py SPEC OUT.bin"""
import sys
sys.path.insert(0, "/home/user/degree-diameter/research/squads/b48/tools")
import groups
spec, out = sys.argv[1], sys.argv[2]
T = groups.table(spec)
groups.check(T)
groups.write_bin(T, out)
print(len(T), spec)
