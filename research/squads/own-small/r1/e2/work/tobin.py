# converts groups/t<N>.txt (G N id abel + N rows) into groups/g<N>_<id>.bin (int32 N, N*N uint16) and .info
import sys, os, struct, array
G='/home/user/degree-diameter/research/squads/own-small/r1/e2/groups'
for fn in sys.argv[1:]:
    lines = open(os.path.join(G, fn)).read().split('\n')
    i = 0
    while i < len(lines) and lines[i].startswith('G '):
        _, N, gid, ab = lines[i].split(); N = int(N); gid = int(gid)
        rows = [list(map(int, lines[i+1+a].split())) for a in range(N)]
        base = os.path.join(G, f"g{N}_{gid:04d}")
        with open(base + '.bin', 'wb') as o:
            o.write(struct.pack('<i', N))
            arr = array.array('H', [x for r in rows for x in r]); arr.tofile(o)
        open(base + '.info', 'w').write(f"{N} {gid} abelian={ab}\n")
        i += 1 + N
print('done', sys.argv[1:])
