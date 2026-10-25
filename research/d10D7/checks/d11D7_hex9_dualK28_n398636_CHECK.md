# (11,7) 398,636: X(phi) over H(9), phi a duality, all 28 absolute flags freed (56 hubs)

Spin-off of the cell-10-7 job (Opus, 2026-10-24). Previous (11,7) record 398,606 (exp2-squad, K = 13); table 398,580.

Construction. H(9) is self-dual (q = 3^2). `research/d10D7/dual/dualfind.c` finds a polarity theta of the subhexagon
H(3) (the points of H(9) with coordinates in GF(3)) and extends it to a duality phi of H(9) (phi^2 fixes exactly the
728 elements of H(3)); its absolute flags (phi(p) = l, phi(l) = p, p on l) are the 28 flags of the Ree-Tits ovoid of
H(3). X(M) with M = phi (exp2 construction, research/squads/exp2/hexd7/README.md), all 28 absolute flags freed,
hub graph random 4-regular on 28+28 hubs. Why no search is needed: the single-pair cover condition is
M(S'(p)) = S(l); a duality with phi(p) = l and phi(l) = p maps S'(p) (points at distance 4 from p, not via l) onto
S(l) (lines at distance 4 from l, not via p), for every absolute flag at once. `d7hex grow ... ` (resume mode,
no GROW) reports cost 0 for all 56 freed sources.

Rebuild and check (from research/d10D7):
    gcc -O3 -o hexgen2 hexgen2.c && ./hexgen2 9
    gcc -O2 -o dual/dualfind dual/dualfind.c && dual/dualfind hex/hex_q9.bin dual/d9      # d9.phi, d9.abs (28 flags)
    python3 mkhub.py rnd 28 4 5 dual/hg28_d4.txt
    python3 dual/mksol.py 9 66430 dual/d9.phi dual/d9.abs dual/hg28_d4.txt dual/x9_dual_K28.sol
    gcc -O3 -o d7hex d7hex.c -lm && ./d7hex edges hex/hex_q9.bin ../frontier/sols/d11D7_hex9_dualK28_n398636.sol g.edges
    gcc -O3 -o apsp ../lifts/coordinator_check/apsp.c && ./apsp g.edges 11 7

apsp (all pairs, no symmetry assumed), 2026-10-24 22:57 UTC:
    n=398636 edges=2192386 degree min=7 max=11 bipartite=yes diameter=7
    RESULT VALID d=11 D=7 n=398636
Edge list sha256: d0a8a4dbe773b27784abd7bbfc2ba0339db4cdc90291e937bc245b8c6277ae88
