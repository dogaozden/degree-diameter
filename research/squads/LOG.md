# Haiku squad log

One entry per squad round (see .claude/skills/haiku-squad/SKILL.md). Started Oct 23, 2026.


## 2026-10-25, raise2-5-9 (round 2 of the (5,9) cell), claude/raise2-5-9-record-lt2t4o

- Record at start: 29,480 (round 1). Notes: research/squads/cells/raise-d5D9.md, section "Round 2".
- Orbit (symmetric S) for Δ = 5 is closed: k = 2 measured at cost ~1,100 (random S: 2); k = 3 single-orbit shape
  (`EXHAUST=1` mode added to research/structured/haar_sym.c, all shapes enumerated): best cost 42 at PSL(2,31),
  24 at SL(2,13) × Z_7.
- Round 1's generator dropped all odd-q SL/PSL/PGL groups (prime_power bug). Screened the corrected list: no candidate
  better than round 1's second tier; annealing at 120–300 s on the top four: costs 10–18.
- Four untried metacyclic groups at 150 s: best costs 6–16. Stopped the rest of the queue.
- Long run 1,200 s on Z_422⋊35 (r = 5), seed 204: cost 0 at 220 s → **record 29,540** (N = 14,770), build_haar2 and apsp VALID.
  File research/frontier/sols/d5D9_meta_422_35_5_s204_n29540.txt.
