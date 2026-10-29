#!/usr/bin/env python3
"""Collect the result lines of check_results.txt (copied from the raw tool output of each remote check worker) into
one check file per candidate, and state whether the source ranges cover 0..n with every range VALID.
usage: assemble_checks.py      (writes d*D7/checks/<cell>.check.txt)"""
import os
import re
from collections import defaultdict

HERE = os.path.dirname(os.path.abspath(__file__))
INFO = {   # cell key -> (folder, n, d, sha256 of the edge list, solution file)
    'd17D7(5,693,790)': ('d17D7', 5693790, 17, '50f886bcca10c08110e48a48222e4f314d3c5427a93ed4cc62fe912097590dcd',
                         'd17D7_hex13_typedwhisk_n5693790.sol'),
    'd18D7(7,290,828)': ('d18D7', 7290828, 18, 'b8b2137f23bc52f398774e3c528309014ae5dec368bfd8f36c56adf9524418e8',
                         'd18D7_hex13_typedwhisk_n7290828.sol'),
    'd15D7(2,509,944)': ('d15D7', 2509944, 15, 'b8ee89cc3b9c9610a9ec6b9b75276e3885aeda78b2b5f588aff1a4a8f4142ac1',
                         'd15D7_hex11_typedwhisk_clpsl31_n2509944.sol'),
    'd15D7(2,512,488)': ('d15D7', 2512488, 15, 'b1ef7d70d7ca21e35dee39f628cb50e3424b80168b1be0b404a248b7db12804d',
                         'd15D7_hex11_typedwhisk_clmeta673x24_n2512488.sol'),
    'd18D7(7,309,092)': ('d18D7', 7309092, 18, '314d5db9f3f3c4af613a56f09f93bcf149d215603adc70ba3ddb4db4deace37d',
                         'd18D7_hex13_typedwhisk_clpsl41_n7309092.sol'),
    'd16D7(4,081,410)': ('d16D7', 4081410, 16, '1bc34853dd30ddbd2483e5a0f90c62bd3e8acf12d5f52ee0a6950008df3c879a',
                         'd16D7_hex13_typedwhisk_nu0_n4081410.sol'),
    'd17D7(5,693,959)': ('d17D7', 5693959, 17, 'bb3c24f77d1d152916163b667d69a77a617820619762fb954fd45373601ab80f',
                         'd17D7_hex13_typedwhisk_nu0_n5693959.sol'),
    'd19D7(11,316,940)': ('d19D7', 11316940, 19, 'd71baea19994d2fb013823260b5c8f44e8407207eaa52c0b24fcc78dd1fc7fc1',
                          'd19D7_hex16_typedwhisk_nu0_n11316940.sol'),
    'd20D7(15,795,219)': ('d20D7', 15795219, 20, 'f9e6399daa20c5d1022acb10f068a19303d3ba10b38cc0c8c1e18f00d1d0dbba',
                          'd20D7_hex16_typedwhisk_nu0_n15795219.sol'),
}
rows = defaultdict(list)
for line in open(os.path.join(HERE, 'check_results.txt')):
    if line.startswith('#') or not line.strip():
        continue
    key = line.split()[0]
    rows[key].append(line.rstrip('\n'))
for key, lines in rows.items():
    if key not in INFO:
        continue
    folder, n, d, sha, sol = INFO[key]
    ranges = []; ok = True
    for l in lines:
        m = re.search(r'sources=(\d+)\.\.(\d+)', l)
        lo, hi = int(m.group(1)), int(m.group(2))
        ranges.append((lo, hi))
        ok &= (f'RESULT VALID d={d} D=7 n={n}' in l and f'n={n} ' in l and 'bipartite=yes' in l and 'diameter=7' in l
               and f'max={d}' in l)
    ranges.sort()
    cover = ranges and ranges[0][0] == 0 and ranges[-1][1] == n and all(a[1] == b[0] for a, b in zip(ranges, ranges[1:]))
    os.makedirs(os.path.join(HERE, folder, 'checks'), exist_ok=True)
    out = os.path.join(HERE, folder, 'checks', f'{folder}_n{n}.check.txt')
    with open(out, 'w') as f:
        f.write(f'# {key}: all-pairs check with research/synthetic/conics/apsp_fast.c (cc -O3 -march=native -pthread; BFS '
                f'from every source of the range, no symmetry assumed), split into source ranges on remote check '
                f'workers (check_sessions.txt). Each worker rebuilt the graph from research/frontier/sols/{sol} with '
                f'typed_build.py build and confirmed the edge list sha256 {sha}.\n')
        f.write('# Lines copied from the raw tool output (cat /tmp/check.out) in each worker transcript:\n')
        f.write('\n'.join(sorted(lines, key=lambda l: int(re.search(r'sources=(\d+)', l).group(1)))) + '\n')
        f.write(f'# ranges cover 0..{n} exactly: {bool(cover)}; every range VALID with n, max degree {d}, bipartite, '
                f'diameter 7: {ok}\n')
        if cover and ok:
            f.write(f'=> every vertex reaches every vertex within 7: diameter 7, bipartite, maximum degree {d}: valid '
                    f'for ({d},7), n = {n}.\n')
    print(key, 'ranges', len(ranges), 'cover', bool(cover), 'all valid', ok, '->', os.path.relpath(out, HERE))
