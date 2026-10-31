"""Rebuild the Haar graph H(SL(2,17), S) from S alone (2x2 matrices mod 17) and print its sha256.
usage: rebuild_from_S.py S.txt edges.txt   (S.txt: d lines 'a b c d', first line the identity)"""
import sys
from sl17lib import parse_S, write_edge_list, sha256_file

S = parse_S(open(sys.argv[1]).read())
n, m = write_edge_list(S, sys.argv[2])
print(f"n={n} edges={m} d={len(S)} sha256(edges)={sha256_file(sys.argv[2])}")
