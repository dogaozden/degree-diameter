# Reorder candidates: w2 screen cost first (split: sweep_table.tsv; non-split: nsA.tsv if the same s), then dk.

H = "/home/user/degree-diameter/research/squads/handsoff-49/"
split_cost = {}
for line in open(H + "w2/sweep_table.tsv"):
    f = line.split()
    if len(f) >= 6: split_cost[(int(f[0]), int(f[1]), int(f[2]), int(f[3]))] = float(f[5])
ns_cost = {}
for line in open(H + "w2/nsA.tsv"):
    f = line.split()
    if len(f) >= 6:
        try: ns_cost[(int(f[0]), int(f[1]), int(f[2]), int(f[3]), int(f[4]))] = float(f[5])
        except ValueError: pass
rows = [l.rstrip("\n").split("\t") for l in open("cand_list.tsv")][1:]
out = []
for dk, N, m, k, r, s, d, typ in rows:
    N, m, k, r, s, dk = map(int, (N, m, k, r, s, dk))
    if typ == "split":
        c = split_cost.get((N, m, k, r), 99.0)
    else:
        c = ns_cost.get((N, m, k, r, s), 99.0)
    out.append((c, dk, N, m, k, r, s, typ))
out.sort()
with open("cand_ordered.tsv", "w") as fh:
    fh.write("dk\tN\tm\tk\tr\ts\td\ttype\n")
    for c, dk, N, m, k, r, s, typ in out:
        fh.write("%d\t%d\t%d\t%d\t%d\t%d\t%d\t%s\n" % (dk, N, m, k, r, s, dk // max(k,1), typ))
print("cost known:", sum(1 for o in out if o[0] < 99), "unknown:", sum(1 for o in out if o[0] >= 99))
import collections
print(collections.Counter(o[0] for o in out if o[0] < 99).most_common(8))
