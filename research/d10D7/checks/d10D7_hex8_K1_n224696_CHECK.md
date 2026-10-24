# (10,7) ≥ 224,696: generalized hexagon H(8), three levels, one freed pair with hubs

Construction X(M) of research/squads/exp2/hexd7/README.md (master) at q = 8: vertices (v, i), v a point or line of
the split Cayley hexagon H(8), i ∈ Z3; hexagon edges in every level and (p, i) ~ (M(p), i+1) for a bijection M.
That is the table graph (3·|H(8)| = 224,694, Δ = 10). One point p is freed: its three M-edges are removed and two hubs
are added (z ~ (p,0),(p,1),(p,2) and z' ~ (M(p),0),(M(p),1),(M(p),2)), +2 vertices. M near the pair is the algebraic
cover of d7hex.c (cost 0 at once).

H(8) needs even q, so the hexagon comes from research/d10D7/hexgen2.c (research/p4/d6/hexgen.c only does q = p, p²).

Rebuild and check (from research/d10D7):

    gcc -O2 -o hexgen2 hexgen2.c && mkdir -p hex && ./hexgen2 8          # hex/hex_q8.bin, sha256 66a11ff04cfeb03d5e64b490352da1662717dd2be4f6025e358b297c0ee486e5
    gcc -O3 -o d7hex ../squads/exp2/hexd7/d7hex.c -lm
    ./d7hex edges hex/hex_q8.bin ../frontier/sols/d10D7_hex8_K1_n224696.sol x.edges
    gcc -O3 -o apsp ../lifts/coordinator_check/apsp.c && ./apsp x.edges 10 7

Results (2026-10-24, cloud session, branch claude/cell-10-7-resume-5fivf6):
- found by `SKIPFULL=1 ./d7hex search hex/hex_q8.bin 1 1 60 out.sol 0 1` (mode 0, algebraic cover, seed 1)
- apsp.c (all pairs, no symmetry, 1 m 41 s): `n=224696 edges=1123473 degree min=3 max=10 bipartite=yes diameter=7`,
  `RESULT VALID d=10 D=7 n=224696`
- sha256 of the solution file: 8340721065d521e69325e0f25b6a8ebcf52be96f68182822e3e05ced46651028
- sha256 of the edge list written by d7hex edges: 726a860b377e9773dae9357b35978550836eed0c4c96a79055c35222e9f5f05c
