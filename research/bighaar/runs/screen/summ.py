import sys, re, glob, statistics as st
for f in sorted(glob.glob('rand_*.log')):
    txt = open(f).read()
    mu = re.search(r'mu=([\d.]+)', txt).group(1)
    rows = re.findall(r'sample \d+ cost (\d+) .*?full (\d+) screen (\d+)', txt)
    if not rows: continue
    cost = [int(a) for a, b, c in rows]; fx = [int(b) for a, b, c in rows]; free = [(int(a) - int(b)) / 5 for a, b, c in rows]
    agree = all(b == c for a, b, c in rows)
    print('%-22s mu=%5s n=%2d cost mean %5.1f min %3d | fixed mean %4.1f | free orbits mean %4.1f min %3.0f | screen agrees %s' % (f[5:-4], mu, len(rows), st.mean(cost), min(cost), st.mean(fx), st.mean(free), min(free), agree))
