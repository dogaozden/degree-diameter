#!/usr/bin/env python3
"""Scorer for pairwise NON-COLLINEAR point sets of H(q) (card c2, round 5).
A set S of point indices is valid iff every line of the hexagon file contains at most one point of S.
Parses hex_q9.bin itself (header int32 q, N, L; L*(q+1) int32 line point indices; N*7 uint8 coordinates).
usage: score_ncol.py HEXFILE IDXFILE   -> prints 'RESULT VALID m' or 'RESULT INVALID m violations=k'
(IDX file: one point index per line, '#' lines and blank lines ignored; the first token of each line is used.)"""
import sys
import numpy as np

def read_hex(path):
    raw = open(path, 'rb').read()
    q, N, L = (int(v) for v in np.frombuffer(raw[:12], dtype=np.int32))
    lines = np.frombuffer(raw[12:12 + 4 * L * (q + 1)], dtype=np.int32).reshape(L, q + 1).astype(np.int64)
    return q, N, L, lines

def read_idx(path):
    out = []
    for line in open(path):
        s = line.strip()
        if not s or s.startswith('#'): continue
        out.append(int(s.split()[0]))
    return out

def score(hexfile, idx):
    q, N, L, lines = read_hex(hexfile)
    if any(i < 0 or i >= N for i in idx):
        return False, len(idx), 'index out of range'
    if len(set(idx)) != len(idx):
        return False, len(idx), 'duplicate index'
    mark = np.zeros(N, np.int64)
    if idx: mark[np.asarray(idx, dtype=np.int64)] = 1
    cnt = mark[lines].sum(axis=1)               # points of S on each line
    viol = int(np.maximum(cnt - 1, 0).sum())    # surplus points: 0 iff every line has <= 1 point of S
    if viol:
        return False, len(idx), f'{int((cnt >= 2).sum())} lines with >= 2 points'
    return True, len(idx), ''

if __name__ == '__main__':
    hexfile, idxfile = sys.argv[1], sys.argv[2]
    idx = read_idx(idxfile)
    ok, m, why = score(hexfile, idx)
    if ok:
        print(f'RESULT VALID {m}')
    else:
        print(f'RESULT INVALID {m} {why}')
