"""Scan the Potocnik-Spiga-Verret census of cubic vertex-transitive graphs (Census3valentVT.zip, graphsym.net) for
bipartite graphs of diameter <= D on lo..hi vertices.  Vertex-transitive => one BFS gives the diameter.
Usage: python3 -I cvt_scan.py ZIP lo hi D"""
import sys, zipfile
from collections import deque

def main():
    zpath, lo, hi, D = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
    z = zipfile.ZipFile(zpath)
    stats = {}
    with z.open('Census3valentVTgraphs.txt') as f:
        hdr = None
        for raw in f:
            line = raw.decode().strip()
            if not line:
                continue
            if '|' in line and 'GrphUnd' in line:
                n, i = map(int, line.split('|')[:2]); hdr = (n, i)
                if n > hi:
                    break
                continue
            if hdr is None or not (lo <= hdr[0] <= hi):
                hdr = None if line.endswith(']') else hdr
                continue
            # adjacency line(s): accumulate until closing bracket
            buf = line
            while not buf.endswith(']'):
                buf += next(f).decode().strip()
            n, i = hdr; hdr = None
            sets = buf.strip('[] ').split('}')
            adj = []
            for s in sets:
                s = s.strip(', {')
                if s:
                    adj.append([int(x) - 1 for x in s.split(',')])
            assert len(adj) == n, (n, i, len(adj))
            col = [-1] * n; col[0] = 0; dist = [-1] * n; dist[0] = 0; q = deque([0]); bip = True
            while q:
                x = q.popleft()
                for y in adj[x]:
                    if dist[y] < 0:
                        dist[y] = dist[x] + 1; col[y] = 1 - col[x]; q.append(y)
                    elif col[y] == col[x]:
                        bip = False
            ecc = max(dist)
            st = stats.setdefault(n, [0, 0, 99, 99])
            st[0] += 1
            if bip:
                st[1] += 1; st[2] = min(st[2], ecc)
                if ecc <= D:
                    print(f"HIT n={n} id={i} bipartite diameter={ecc}", flush=True)
            else:
                st[3] = min(st[3], ecc)
    for n in sorted(stats):
        a, b, eb, enb = stats[n]
        print(f"n={n} graphs={a} bipartite={b} min_diam_bip={eb if b else '-'} min_diam_nonbip={enb if a > b else '-'}")

main()
