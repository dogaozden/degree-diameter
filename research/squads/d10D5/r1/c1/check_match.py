"""check_match.py SETS: print the flaggreedy matching size of each line of SETS ("p:l p:l ...")."""
import sys, random
sys.argv = ['flaggreedy.py', 'gq/gq_q7.bin', '1', '0']
src = open('flaggreedy.py').read().split('flags = []')[0]
exec(compile(src, 'flaggreedy_head', 'exec'))
for line in open('sets_test.txt'):
    fl = [tuple(map(int, t.split(':'))) for t in line.split()]
    sz, _ = matching(fl)
    print(len(fl), 'python matching', sz, 'deficiency', N - sz, flush=True)
