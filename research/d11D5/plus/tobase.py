import json, sys
d = json.load(open(sys.argv[1])); L = d["Lnew"]; sg = d["sigma"]; n = len(L)
with open(sys.argv[2], "w") as f:
    f.write(f"{n} {len(L[0])}\n")
    for s in L: f.write(" ".join(map(str, s)) + "\n")
    f.write("\n".join(map(str, sg)) + "\n")
