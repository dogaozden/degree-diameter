#!/usr/bin/env python3
"""Independent NB-4 coverage count for one Haar controller S (uses nb_check.uncovered).
usage: python3 -B one_S_check.py TABLE e a b c   (TABLE as written by groups_scan.py; S = [e,a,b,c] as element indices)"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from nb_check import load, uncovered
path = sys.argv[1]; S = list(map(int, sys.argv[2:6]))
m, T = load(path)
print('S =', S, ' independent uncovered per side (summed over all starts, A,B):', uncovered(m, T, S))
