# w10 NOTES (handsoff-49): Haar graphs of centreless groups with small abelianization

Start: 2026-10-31 23:13 UTC. Planned end: 01:15 UTC. Last update: 23:17 UTC.

## Setup
- mk.py: group toolkit. `semidirect_vec(p, d, gens)` builds V x| H over GF(p) from matrix generators; `props(T)`
  gives N, centre size, |G'|, abelianization size, sampled associativity check; `write_bin` writes haar_tab .bin.
- build1.py: builds the card's groups into tabs/NAME.bin (props checked: centre 1 everywhere, ab as the card says).
- screen.sh SECS "SEEDS" NAME...: runs `haar_tab 4 9 SECS seed 8 runs/NAME_sSEED.sol tab tabs/NAME.bin 1`,
  appends to screen.tsv.

## Card groups (order N, centre, |G^ab|)
| name | N | ab | build |
| A5xAGL17 | 2520 | 6 | perm 5 x agl1 7 |
| S5x_Z7Z3 | 2520 | 6 | perm S5 x meta 7 3 2 |
| Z17sq_Z9 | 2601 | 9 | Frobenius, companion of irreducible quadratic of order 9 |
| Z29sq_Z3 | 2523 | 3 | Frobenius, [[0,28],[1,28]] |
| Z3p5_Z11 | 2673 | 11 | Frobenius, companion of quintic factor of Phi_11 over GF(3) |
| Z19sq_Q8 | 2888 | 4 | Q8 in SL(2,19) |
| Z11sq_SL23 | 2904 | 3 | SL(2,3) in SL(2,11) (found by random search, orders checked) |
| ASL25 | 3000 | 1 | perfect, SL(2,5) on GF(5)^2 |
| F7Z3xF13Z12 | 3276 | 36 | product of Frobenius groups |

## Screen results
(see screen.tsv; filled in below as runs finish)
