# Squad round d7fam-r1 (job d7-family, 2026-10-25, ~16:40 UTC)

Inputs (read-only, copy what you need): SQ = /tmp/claude-0/-home-user-degree-diameter/0ecf9576-c77c-5462-b736-5bb1ddd9e678/scratchpad/w/sq
(hex_q{5,7,8,11,13}.bin = split Cayley hexagon H(q) from research/d13D7/hexgen2.c; R_q*.npy base sets; S_q*.npy spreads;
state_*.npz mirrored configurations (R base set, X extra points, L their lines); RH_q*.txt / RL_q*.txt plain freed sets;
mirror_sa5.py / mirror_sa6.py annealers, mirror_build2.py / mirror_build3.py builders+scorers, hexmod.py; setcheck.py;
pack.c, dpack.c ILS codes).

| card | goal | scorer |
|---|---|---|
| c1 | q=11 mirrored set > 768 (cells (13,7),(14,7),(15,7): +2 each per point) | mirror_build2.py STATE 1 OUT hex_q11.bin S_q11.npy |
| c2 | q=13 mirrored set > 813 ((16,7): +2 per point) | mirror_build2.py STATE 1 OUT hex_q13.bin S_q13.npy |
| c3 | q=5 mirrored set > 81 ((7,7)) | mirror_build2.py ... hex_q5.bin S_q5.npy |
| c4 | q=7 mirrored set > 295 ((9,7)) | mirror_build2.py ... hex_q7.bin S_q7.npy |
| c5 | q=8 mirrored set > 229 ((10,7), characteristic 2) | mirror_build3.py ... hex_q8.bin S_q8.npy |
| c6 | non-concurrent line set of H(11) > 8,246 ((14,7): +2 per line up to 8,645) | setcheck.py hex_q11.bin L FILE |
| c7 | non-collinear point set of H(13) > 14,762 ((16,7): +2 per point up to 14,823) | setcheck.py hex_q13.bin P FILE |
| c8 | wildcard: non-concurrent line set of H(13) > 14,823 by an approach no other card uses | setcheck.py hex_q13.bin L FILE |
