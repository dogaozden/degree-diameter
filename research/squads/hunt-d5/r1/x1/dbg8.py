import sys
sys.argv = ['x', 'g392_41.bin', '5', '8', '1']
exec(open('bicoset.py').read().split("if __name__ == '__main__':")[0])
for s in [1,2]:
    rng.seed(s)
    best, st, dcs2, it, _ = run(6, 40, 2, 1)
    print('seed',s,'best',best,'iters',it, 'state', st)
