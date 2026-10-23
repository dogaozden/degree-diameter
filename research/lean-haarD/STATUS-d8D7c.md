# lean-haarD job d8D7c: Δ8·D7 records 41,040 and 43,344

## Done

- **41,040 (`nb_8_7_haar`)**: the earlier branch `claude/lean-haar-d8d7-ecb54e` (commits 18a4335, 646f789) rebased
  onto `origin/master`. Its `Diam7.lean` was dropped in favour of master's. The record module is
  `BipartiteDD/Haar/Record41040.lean`, and `BipartiteDD/Haar/D8D7/Axioms.out.txt` is regenerated:
  `[propext, Classical.choice, Quot.sound]`. Built on master's `haar_isBipartiteDegDiam7_of_equiv`.
- **43,344 (`nb_8_7_43344`)**: proved, `∃ G : SimpleGraph (Fin 43344), IsBipartiteDegDiam G 8 7`.
  Axioms: `[propext, Classical.choice, Quot.sound]` (`BipartiteDD/Haar/D8D7b/Axioms.out.txt`).
  Modules, all under `lean/BipartiteDD/Haar/D8D7b/`:
  - `GF8.lean`: GF(8) = GF(2)[x]/(x³+x+1) as a `CommRing` on `Fin 8` (xor addition, bitwise product `mulN`);
    the axioms are checked by `decide +kernel`.
  - `SL8.lean`: SL(2,8) as matrices over GF8 with det 1, numbered by `Fin 504` (c = 0 block first).
  - `SL8Z43.lean`: SL(2,8) × Z43, numbered by `Fin 21672` (index 43·enc + z).
  - `Check.lean`: the connection set S (from `research/frontier/sols/d8D7_sl_8_43_orb3_s1.txt`) and the word checks.
  - `Stage00`…`Stage11`: the certificates, 1806 indices each, each stage built by `decide +kernel`
    (about 100 s per stage).
  - `Cover.lean`, `Record43344.lean` (`equiv43344`, `nb_8_7_43344`), `Axioms.lean`, `Axioms.out.txt`.
  - Generator: `research/lean-haarD/gen_d8D7b.py SOL OUTDIR`; it re-checks every word by direct multiplication.

## Partial / blocked

Nothing outstanding. Only deprecation warnings (`dif_pos`, copied from SL19).

## Notes

- Build time: stage modules about 100 s each; full `Record43344` chain about 25 min on 4 cores.
- The solution header's convention (bit-polynomial, x³+x+1) was checked: all 8 matrices have det 1 and
  all 21672 elements have A- and B-words of length 6 in S.
- Each of the 12 stage modules was built one at a time; no parallel builds.
