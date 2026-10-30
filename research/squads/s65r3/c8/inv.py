import sys, glob, re, os
res = []
for o in [352,354,356,358,360]:
    for f in sorted(glob.glob(f"/home/user/degree-diameter/research/s65/groups/mc/sg_{o}_*.txt")):
        lines = open(f).read().split()
        m = int(lines[0])
        T = [int(x) for x in lines[1:1+m*m]]
        # check size
        assert len(T) == m*m, (f, len(T))
        # abelian check
        ab = True
        for i in range(m):
            for j in range(i+1, m):
                if T[i*m+j] != T[j*m+i]:
                    ab = False; break
            if not ab: break
        inv = [i for i in range(1,m) if T[i*m+i] == 0]
        name = open(f[:-4]+".name").read().strip()
        res.append((o, len(inv), ab, os.path.basename(f)[:-4], name))
import collections
cnt = collections.Counter()
for o, k, ab, b, name in res:
    cnt[(o, ab, k)] += 1
for key in sorted(cnt):
    print(key, cnt[key])
sel = [r for r in res if (not r[2]) and r[1] > 3]
print("selected", len(sel))
sel.sort(key=lambda r: (r[1], r[0], r[3]))
with open("/home/user/degree-diameter/research/squads/s65r3/c8/groups_sel.txt","w") as fo:
    for o,k,ab,b,name in sel:
        fo.write(f"{b} {k} {name}\n")
print(collections.Counter(r[1] for r in sel))
