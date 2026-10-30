import re, sys
# usage: parse.py ID STRUCT  -> prints one table line, reads h<ID>.log
gid, struct = sys.argv[1], sys.argv[2]
txt = open(f"h{gid}.log").read().splitlines()
total = None
for l in txt:
    m = re.search(r"pair classes=(\d+)", l)
    if m: total = int(m.group(1)); break
done_line = [l for l in txt if l.startswith("DONE")]
pairs = [l for l in txt if l.startswith("PAIR ")]
valid = [l for l in txt if l.startswith("VALID")]
aside = [l for l in txt if l.startswith("ASIDE")]
if done_line:
    fin = "yes"
    d = done_line[0]
    sets = re.search(r"sets=(\d+)", d).group(1)
    minA = re.search(r"minA=(\d+)", d).group(1)
    npairs = total
else:
    fin = "no"
    sets = sum(int(re.search(r"sets=(\d+)", p).group(1)) for p in pairs)
    minA = min([int(re.search(r"minA=(\d+)", p).group(1)) for p in pairs] or [-1])
    npairs = (int(pairs[-1].split()[1]) + 1) if pairs else 0
bunc = [int(re.search(r"Bunc=(\d+)", a).group(1)) for a in aside if "Bunc=" in a]
mb = str(min(bunc)) if bunc else "-"
print(f"{gid} | {struct} | {fin} ({npairs}/{total}) | {sets} | {len(valid)} | {minA} | {mb}")
