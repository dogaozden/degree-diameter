# usage: mk_rm.py out.edges  i c  [i c ...] : remove matching-copy classes (d=i, c) from g18
import sys, pickle
E = pickle.load(open('E18.pkl', 'rb'))
out = sys.argv[1]; sel = set()
args = sys.argv[2:]
for k in range(0, len(args), 2): sel.add((int(args[k]), int(args[k+1])))
kept = [(x, y) for x, y, d, c in E if (d, c) not in sel]
with open(out, 'w') as g:
    g.write("47600\n"); g.writelines(f"{x} {y}\n" for x, y in kept)
print(out, "edges", len(kept))
