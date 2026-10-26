#!/usr/bin/env python3
"""Indices (haar_fast numbering a*k + j, Z_n factor must be 1) of a haar_fast solution / near-miss file."""
import sys, re
L = open(sys.argv[1]).read().split('\n'); hdr = L[0].split()
assert 'n' in hdr and hdr[hdr.index('n') + 1] == '1', "only n = 1 files"
print(" ".join(l.split()[0] for l in L[1:] if l.strip()))
