# Card c8: ι-orbit (x -> x^-1 on words) counting bound for covering G (|G|=384) by the 781 words.
# Words of length 2 and 4 (non-backtracking, plus e) are closed under reversal iota; iota has no fixed
# point on the 780 non-identity words, so they form 390 orbits. Each orbit covers the inverse class
# {g, g^-1} of its value. Covering needs one orbit per non-identity inverse class:
#   (383 + i)/2 <= 390, where i = number of non-identity involutions.
# Count groups (of the 20,169 in inv384.txt) excluded by this, and check the 7 side-A covers and 342_12 are kept.
import re, sys
INV = "/home/user/degree-diameter/research/six-five-384/data/inv384.txt"
COV = "/home/user/degree-diameter/research/six-five-384/data/coverage384.txt"
N = 384
ORBITS = 390
need = lambda i: (N - 1 + i) / 2.0          # classes needed (non-identity inverse classes)
inv = {}
for line in open(INV):
    p = line.split()
    gid = int(p[0])
    m = re.search(r"inv=(\d+)", line)
    inv[gid] = int(m.group(1))                  # involutions in G (includes none for e)
# involution count from inv384 is the number of elements of order 2 in G (identity not counted)
excluded = [g for g, i in inv.items() if need(i) > ORBITS]
exh = set()
acov = set()
for line in open(COV):
    if line.startswith("#"):
        continue
    p = line.split()
    gid = int(p[0])
    if p[1].startswith("exhaustive"):
        exh.add(gid)
    m = re.search(r"Acovered=(\d+)", line)
    if m and int(m.group(1)) > 0:
        acov.add(gid)
print("groups:", len(inv), "max involutions:", max(inv.values()))
print("excluded by orbit count:", len(excluded))
print("excluded among exhaustive order-384 groups:", len([g for g in excluded if g in exh]))
print("side-A covers kept:", sorted(acov - set(excluded)), "of", len(acov))
