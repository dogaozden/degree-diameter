# Independent bcd checks of the two unrecorded D = 10 Haar candidates

bigcheck-dist lead session, 2026-10-25, cloud machine (4 cores, 15 GB), shared with other jobs (1 thread each).
These graphs beat the table cells (15,10) 2,300,326,510 and (16,10) 4,119,507,330. They were found and checked by
other sessions (research/frontier/runs/cloudcheck/, branches below); bcd is a third, separately written checker: the
Haar graph H(G,S) is read as the lift of the dipole over G = SL(2,p) × Z_n (research/projects/bigcheck-dist/
haar2lift.py), group elements are rebuilt from the mat(a,b,c,d) z=Z fields (the index column of the files is ignored),
and BFS runs from one vertex on each side (right multiplications are automorphisms of every such lift).

| cell | file (branch) | sha256 | vertices | bcd build | result |
|---|---|---|---:|---|---|
| (15,10) | d15D10_sl_149_373_orb3f0_s1.txt (claude/bipartite-d15-d10-search-h3rdep) | 6430a3a4e15d3d4881b22ace8f717e455c74996b16c9aaeb34d8fd2faf6e8efa | 2,467,618,800 | -DWB=8 | (running) |
| (16,10) | research/bighaar/runs/d16D10_sl_151_637_orb3_s1.txt (claude/bipartite-16-10-cell-kras4l) | f2a70a0d5bc93765cd0118e5013a6f9e1f9737751f98dfab62f661bb9d502130 | 4,386,127,200 | -DWB=1 | (running) |

Commands:

    gcc -O3 -march=native -fopenmp -DWB=8 -o bcd8 bcd.c; gcc -O3 -march=native -fopenmp -DWB=1 -o bcd1 bcd.c
    python3 haar2lift.py d15D10_sl_149_373_orb3f0_s1.txt d15D10.spec && bcd8 lift d15D10.spec 15 10 --threads 1 --cert d15D10.cert
    python3 haar2lift.py d16D10_sl_151_637_orb3_s1.txt d16D10_637.spec && bcd1 lift d16D10_637.spec 16 10 --threads 1 --cert d16D10_637.cert
