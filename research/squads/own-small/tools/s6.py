"""Decode one sparse6 line (nauty format) into an edge list. Usage: python3 -I s6.py FILE.s6 INDEX(1-based) OUT.edges"""
import sys
def decode(s):
    s = s.strip()
    if s.startswith(':'): s = s[1:]
    data = [ord(c) - 63 for c in s]
    if data[0] < 63: n = data[0]; pos = 1
    elif data[1] < 63: n = (data[1] << 12) | (data[2] << 6) | data[3]; pos = 4
    else: n = 0; [n := (n << 6) | data[2 + i] for i in range(6)]; pos = 8
    k = (n - 1).bit_length()
    bits = []
    for x in data[pos:]:
        for i in range(5, -1, -1): bits.append((x >> i) & 1)
    v = 0; edges = []; i = 0
    while i + 1 + k <= len(bits):
        b = bits[i]; i += 1
        x = 0
        for _ in range(k): x = (x << 1) | bits[i]; i += 1
        if b: v += 1
        if v >= n: break
        if x > v: v = x
        else: edges.append((x, v))
    return n, edges
if __name__ == '__main__':
    lines = [l for l in open(sys.argv[1]) if l.strip() and not l.startswith('>')]
    n, E = decode(lines[int(sys.argv[2]) - 1])
    with open(sys.argv[3], 'w') as o:
        o.write(f"{n}\n"); o.writelines(f"{u} {v}\n" for u, v in E)
    print(n, len(E))
