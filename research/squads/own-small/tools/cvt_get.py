"""Extract graph (n, id) from the cubic VT census zip (Census3valentVT.zip) as an edge list. Usage: python3 -I cvt_get.py ZIP n id OUT"""
import sys, zipfile
zpath, N, ID, out = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), sys.argv[4]
z = zipfile.ZipFile(zpath)
with z.open('Census3valentVTgraphs.txt') as f:
    hdr = None
    for raw in f:
        line = raw.decode().strip()
        if not line: continue
        if '|' in line and 'GrphUnd' in line:
            hdr = tuple(map(int, line.split('|')[:2]))
            if hdr[0] > N: break
            continue
        if hdr != (N, ID):
            continue
        buf = line
        while not buf.endswith(']'): buf += next(f).decode().strip()
        adj = [[int(x) - 1 for x in s.strip(', {').split(',')] for s in buf.strip('[] ').split('}') if s.strip(', {')]
        E = sorted({(min(u, v), max(u, v)) for u in range(len(adj)) for v in adj[u]})
        open(out, 'w').write(f"{len(adj)}\n" + ''.join(f"{u} {v}\n" for u, v in E))
        print(len(adj), len(E)); break
