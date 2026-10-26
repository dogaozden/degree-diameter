import sys
for N in (51, 52, 43, 44):
    tok = open(f"/home/user/degree-diameter/research/squads/own-small/runs/gtxt/g{N}.txt").read().split()
    i = 0
    while i < len(tok):
        n_, gid = int(tok[i+1]), int(tok[i+2]); i += 4
        T = [list(map(int, tok[i+r*N:i+(r+1)*N])) for r in range(N)]; i += N*N
        ab = all(T[a][b] == T[b][a] for a in range(N) for b in range(N))
        p = 5 if N in (51, 52) else 6
        print(p, N, gid, 0 if not ab else 1)
