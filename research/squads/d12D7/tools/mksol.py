"""Write a d7hex-style .sol (read by x5gen2/xgen) with a new freed point list and the matching M of an existing .sol.
Usage: python3 mksol.py BASE.sol FREED.txt OUT.sol
FREED.txt: whitespace-separated point ids (0..N-1). Duplicates are removed; order is kept."""
import sys

def read_sol(fn):
    tok = open(fn).read().split()
    assert tok[0] == "d7hex"
    q, N, K, nv = map(int, tok[1:5])
    i = 6
    freed = list(map(int, tok[i:i + K])); i += K
    hm = int(tok[i + 1]); i += 2 + 2 * hm
    M = list(map(int, tok[i:i + N]))
    assert len(M) == N
    return q, N, freed, M

def main():
    base, ff, out = sys.argv[1:4]
    q, N, _, M = read_sol(base)
    seen, F = set(), []
    for x in map(int, open(ff).read().split()):
        assert 0 <= x < N
        if x not in seen:
            seen.add(x); F.append(x)
    with open(out, "w") as f:
        f.write(f"d7hex {q} {N} {len(F)} 0 freed\n" + " ".join(map(str, F)) + "\nhubs 0\n" + " ".join(map(str, M)) + "\n")
    print(f"q={q} N={N} K={len(F)} -> {out}")

if __name__ == "__main__":
    main()
