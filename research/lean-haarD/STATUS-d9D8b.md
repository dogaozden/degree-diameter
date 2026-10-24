# STATUS d9D8b: Δ9·D8 record, 511,056 vertices (SL(2,27) × Z13)

**Status: done.** `nb_9_8_511056` is kernel-checked.

    theorem nb_9_8_511056 : ∃ H : SimpleGraph (Fin 511056), BipartiteDD.IsBipartiteDegDiam H 9 8

Axioms (`lean/BipartiteDD/Haar/D9D8b/Axioms.out.txt`): `'nb_9_8_511056' depends on axioms: [propext, Classical.choice, Quot.sound]`.
No `sorry`, `admit`, `native_decide` or `axiom` in `lean/BipartiteDD/Haar/D9D8b/`.

Target theorem (to be built): `theorem nb_9_8_511056 : ∃ H : SimpleGraph (Fin 511056), BipartiteDD.IsBipartiteDegDiam H 9 8`.

## Record
- Group `G = SL(2,27) × Z13`, `|G| = 19656 · 13 = 255528`; graph on `G ⊕ G`, 511056 vertices, degree 9.
- `S` is `research/frontier/sols/d9D8_sl_27_13_orb3_s1.txt`. `build_haar2.py` confirms: ecc 8 from both sides, n = 511056, degree 9, no duplicate edges, VALID.

## Modules (`lean/BipartiteDD/Haar/D9D8b/`)
- `GF27.lean`: GF(27) = GF(3)[x]/(x³+2x+1) on `Fin 27`; ring laws by `decide +kernel`.
- `SL2.lean`: `SL(2,27)` as a `Group`, numbering onto `Fin 19656` (`quad`, `encT`, checks in 10 chunks of 2000).
- `Base.lean`: `G`, `equivG : G ≃ Fin 255528`, `haarVert : G ⊕ G ≃ Fin 511056`.
- `Gens.lean`: nine generators (entries as `ofN k`; numerals of GF(27) would reduce mod 3).
- `Check.lean`, `Stage00 … Stage57`: 58 stages of 4446 codes (last 2106), `decide +kernel`.
- `Cover.lean`, `Covers.lean`, `Record.lean` (reuses `BipartiteDD.Haar.D9D8.Even8`), `Axioms.lean` / `Axioms.out.txt`.
- `lean/Axioms.lean` was not extended, for the same reason as D9D8 and D7D8b: it imports every record. The check lives in `D9D8b/Axioms.lean`.
- Generator: `research/lean-haarD/d9D8b/gen_d9D8b.py`.

## Build measurements
- Stage00: 157 s, peak RSS about 12.4 GB (measured with a wrapper that sums `lean` RSS).
- Stages 01–56: 145–163 s each, peak RSS about 12.8 GB. Stage57 (2106 codes): 64 s, 7.0 GB.
- Built one at a time, all rc=0: Stage00–57, Cover, Covers, Record, then `Axioms` checked with `lake env lean`.
- Largest stage: 4446 codes in one `decide +kernel`, about 12.8 GB peak.

## Largest stage that built
All 58 stages (`Stage00 … Stage57`, 4446 codes each, the last 2106), then `Cover`, `Covers`, `Record`, `Axioms`.

## Obstacles met (resolved)
- `decide +kernel` over `∀ n < 19656` for the numbering checks ran out of memory (exit 137). Split into 10 chunks of 2000.
- `(21 : GF(27))` is `21 mod 3 = 0`. Gens entries now use `ofN`.

## Deviations from the brief
- **Setup.** `elan` 4.2.4 from the pinned release, then `lake exe cache get`. The installer's `latest` URL returned 502 through the proxy; the versioned release URL worked.
- **Branch.** The brief says `lean-haarD-d9D8b`. The session's designated branch is `claude/d9d8b-nb-9-8-511056-jrywn1`, and that is where it is pushed. Draft PR #250.
- **Attribution.** The `Co-Authored-By` line naming the model is omitted; the system instructions bar model identifiers in commits.
