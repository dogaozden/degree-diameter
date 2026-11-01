"""canonical certificates via nauty-labelg on graph6; usage: iso.py files... -> prints cert-hash counts"""
import sys, subprocess, collections, hashlib
sys.path.insert(0, __file__.rsplit('/',1)[0]); from gutil import load
def g6(n, adj):
    bits = []
    for j in range(n):
        s = set(adj[j])
        for i in range(j): bits.append(1 if i in s else 0)
    out = chr(63 + n) if n < 63 else chr(126) + chr(63 + (n >> 12 & 63)) + chr(63 + (n >> 6 & 63)) + chr(63 + (n & 63))
    while len(bits) % 6: bits.append(0)
    for k in range(0, len(bits), 6):
        v = 0
        for b in bits[k:k+6]: v = 2*v + b
        out += chr(63 + v)
    return out
def certs(files):
    lines = []
    for fn in files:
        n, E, adj = load(fn); lines.append(g6(n, adj))
    r = subprocess.run(["nauty-labelg", "-q"], input="\n".join(lines) + "\n", capture_output=True, text=True)
    return r.stdout.split()
if __name__ == "__main__":
    files = sys.argv[1:]; cs = certs(files)
    cnt = collections.Counter(cs)
    print(len(files), "graphs,", len(cnt), "iso classes")
    for c, k in cnt.most_common(): 
        ex = files[cs.index(c)]; print(k, hashlib.md5(c.encode()).hexdigest()[:10], ex)
