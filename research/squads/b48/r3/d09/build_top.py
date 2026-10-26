import sys, json
sys.path.insert(0, "/home/user/degree-diameter/research/squads/b48/tools")
import groups, numpy as np
rs = [json.loads(l) for f in ["proxy_a.jsonl","proxy_b.jsonl","proxy_c.jsonl","proxy_d.jsonl"] for l in open(f) if l.strip()]
rs.sort(key=lambda r: r["deficit"])
top = rs[:int(sys.argv[1])]
for i, r in enumerate(top):
    T = groups.table(r["spec"])
    fn = f"/home/user/degree-diameter/research/squads/b48/r3/d09/tabs/g{i:02d}.bin"
    groups.write_bin(T, fn)
    print(i, r["deficit"], r["N"], r["spec"], fn, flush=True)
