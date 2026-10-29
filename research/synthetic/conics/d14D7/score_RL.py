"""Scorer for squad conics-r3: size of a dual segment set of lines of H(11).

A set G of lines is a dual segment set if, for every line L in G, the other lines of G that meet L all pass through
one point of L.  Input: a text file of line ids (0..177155, the line numbering of hex_q11.bin, whitespace separated).
Prints  SCORE <|G|>  if valid, else INVALID <reason>.
Usage: python score_RL.py FILE"""
import sys
import numpy as np

b = open('/home/user/degree-diameter/research/p4/d6/hex/hex_q11.bin', 'rb').read()
q, N, Lc = (int(x) for x in np.frombuffer(b[:12], dtype=np.int32))
LP = np.frombuffer(b[12:12 + 4 * Lc * (q + 1)], dtype=np.int32).reshape(Lc, q + 1).astype(np.int64)
G = np.array([int(v) for v in open(sys.argv[1]).read().split()], dtype=np.int64)
if len(G) == 0 or G.min() < 0 or G.max() >= Lc:
    print('INVALID ids out of range'); sys.exit(1)
if len(np.unique(G)) != len(G):
    print('INVALID repeated ids'); sys.exit(1)
cnt = np.zeros(N, np.int64)
np.add.at(cnt, LP[G].reshape(-1), 1)
bad = ((cnt[LP[G]] >= 2).sum(axis=1) > 1)
if bad.any():
    print(f'INVALID {int(bad.sum())} lines meet other lines of the set in two or more of their points'); sys.exit(1)
print(f'SCORE {len(G)}')
