"""Convert an "n m" + edge-list text file to the records JSON format. Usage: txt2json.py in.txt out.json case"""
import json, sys
with open(sys.argv[1]) as f:
    n, m = map(int, f.readline().split())
    edges = [list(map(int, line.split())) for line in f]
assert len(edges) == m
with open(sys.argv[2], 'w') as f:
    json.dump({'case': sys.argv[3], 'value': n, 'output': [n, edges]}, f)
print(n, m)
