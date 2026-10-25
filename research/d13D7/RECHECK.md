# Re-checking the D = 7 hexagon graphs of job cell-13-7

All commands from research/d13D7/. Compile once:

    gcc -O2 -o hexgen hexgen.c -lm && gcc -O2 -o hexgen2 hexgen2.c -lm && mkdir -p hex
    gcc -O3 -march=native -fopenmp -o apsp_wide apsp_wide.c    # apsp.c with 512-source batches, OpenMP
    gcc -O3 -march=native -fopenmp -o apsp_src apsp_src.c      # same, sources from a file
    gcc -O3 -march=native -fopenmp -o multi multi.c            # (2r+1)-copy builder
    gcc -O2 -o d7hex ../squads/exp2/hexd7/d7hex.c -lm          # exp2's three-copy builder (d7hex format)
    for q in 5 7 9 11 13; do ./hexgen $q; done; ./hexgen2 8     # hex/hex_q*.bin (hexgen2 adds GF(8))

Three copies (Δ = q+2): rebuild from the d7hex solution and run the reference checker.

    ./d7hex edges hex/hex_q11.bin ../frontier/sols/d13D7_hex11_R756_n1064448.sol out.edges && ./apsp_wide out.edges 13 7
    (13,7) d13D7_hex11_R756_n1064448.sol  q=11   (also: python3 build_d13D7.py sets/R756_r4c1_coords.txt out.edges)
    (7,7)  d7D7_hex5_R72_n23580.sol       q=5
    (9,7)  d9D7_hex7_R288_n118224.sol     q=7
    (10,7) d10D7_hex8_R217_n225128.sol    q=8   (hex file from hexgen2)
    (11,7) d11D7_hex9_dual_R3958_n406496.sol q=9

More copies (Δ = q+1+r): rebuild with tools/multi_sol.py, then check. Full all-pairs (apsp_wide) works but is long
for the larger ones; (x, i) -> (x, i+1) with the hubs fixed is an automorphism, so BFS from all level-0 vertices
(ids 0 .. 2N-1, N = number of points) and all hubs (ids (2r+1)·2N .. n-1) gives the exact diameter:

    python3 tools/multi_sol.py build ../frontier/sols/d14D7_hex11_R756_n1774584.sol hex/hex_q11.bin out.edges
    python3 -c "N=177156; L=5; n=1774584; print('\n'.join(map(str, list(range(2*N)) + list(range(L*2*N, n)))))" > src.txt
    ./apsp_src out.edges 14 7 src.txt
    (12,7) d12D7_hex9_dual_R2459_n673892.sol   q=9,  r=2, N=66,430,  n=673,892
    (14,7) d14D7_hex11_R756_n1774584.sol       q=11, r=2, N=177,156, n=1,774,584
    (15,7) d15D7_hex11_R756_n2484720.sol       q=11, r=3, N=177,156, n=2,484,720
    (16,7) d16D7_hex13_R500_n4024340.sol       q=13, r=2, N=402,234, n=4,024,340

Every check file in checks/ repeats its own commands and the recorded output.
