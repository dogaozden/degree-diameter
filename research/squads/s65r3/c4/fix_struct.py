import re, sys
# rewrite the structure field of table.txt rows from exp_<id>.out (GAP may wrap the EXPORTED line)
rows = open("table.txt").read().splitlines()
out = []
for r in rows:
    parts = r.split(" | ")
    if len(parts) >= 7 and parts[0] != "order_id":
        gid = parts[0]
        try:
            txt = open(f"exp_{gid}.out").read()
            m = re.search(r"gens=\s*\d+\s+(.*)", txt, re.S)
            if m:
                parts[1] = " ".join(m.group(1).split())
        except FileNotFoundError:
            pass
        r = " | ".join(parts)
    out.append(r)
open("table.txt", "w").write("\n".join(out) + "\n")
