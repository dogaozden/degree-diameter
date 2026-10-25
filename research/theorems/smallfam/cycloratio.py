"""Solve rate of the groups the cyclotomic bound leaves open, as a function of x = N / B(k, o).
Usage: python3 cycloratio.py runs/cyclobound_d3D*.txt"""
import sys
bins = [0, 0.4, 0.5, 0.6, 0.7, 0.8, 0.9, 1.0001]
cnt = [[0, 0] for _ in bins[:-1]]
for fn in sys.argv[1:]:
    for line in open(fn):
        f = line.split()
        if len(f) < 9 or f[8] != 'open':
            continue
        N = int(f[4]); sol = int(f[6].split('=')[1]); B = int(f[7].split('=')[1])
        x = N / B
        for i in range(len(bins) - 1):
            if bins[i] <= x < bins[i + 1]:
                cnt[i][0] += 1; cnt[i][1] += sol > 0
print('N/B range     open groups  solving  rate')
for i in range(len(bins) - 1):
    g, s = cnt[i]
    print(f'[{bins[i]:.1f}, {min(bins[i+1],1.0):.1f})  {g:11d} {s:8d}  {100.0 * s / g if g else 0:5.1f} %')
