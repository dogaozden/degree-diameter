# Handoff: job thm-order2 (second session, branch claude/thm-order2-symmetry-wejgw7)

Main write-up: research/theorems/ORDER2.md (short answer first; ranked sections in §6). Files:
research/theorems/order2/ (§7 of ORDER2.md lists them). The first session's branch was
claude/thm-order2-symmetry-gap-4e2nmi; this branch carries both sessions (rebased on master, PR #312).

## State at the end of the second session

No new record in this session (the first session's (13,8) 6,999,552 stands). Anneals, all resumable from
research/theorems/order2/runs/ckpt/*.ckpt with the same command plus CKPT= (launch scripts in runs/r2/):
- (15,9) SL(2,64)×Z403, order 6 (runs/r2/launch_159.sh, launch_159b.sh with OSTAB=1): best cost 2 in the OSTAB seed 2
  (an159_sl64_403_k6sub3_ostab_s2.ckpt). Only the order-3 pair of SL(2,2) = Fix(α) is uncovered, on side B
  (UNCPRINT=1 lists it). A full scan of the 3-element slot (SCANSUB=1) found no completion. So one of the
  6-orbits must change. Use OSTAB=1: plain energy stalls at the involutions of Fix(α), Fix(α²).
- (13,10) SL(2,16)²×Z21, order 6: best 4 after 7,697 evaluations in 4.5 h (an1310_sl16sq_21_k6_s1.ckpt), about 2 s per
  evaluation on one thread; the rule's median is 1.4·10⁴ evaluations.
- (15,8) SL(2,8)²×Z37, 6+6+3: best 6 (an158_*_s1.ckpt). (13,9) SL(2,64)×Z133: best 23; out of reach by the refined
  rule (μ_A 16.8).

## What the second session found (details in ORDER2.md)
1. Why order 2 beat order 3 at (6,8): on SL(2,25) the order-3 space has only 8,773 classes of equivalent Haar graphs,
   all sampled; the best has cost 2. The order-2 spaces have 2.68·10⁶ (Frobenius, exactly 1 valid class) and
   3.42·10⁷ (conjugation, about 40–60 valid) classes (§3.4).
2. The first session's twisted-cycle charge is half right: the short cycles are paid as avoidance, and
   P(valid) ≈ P(no twisted 4- or 8-cycle)·e^{−(μ_A⁰−6)} fits four order-2 spaces to 0.4 nats. Its long-cycle charge
   and absolute level are not seen. The four-way anneal ranking (Frobenius 5/6 seeds against conjugation 2/6) is the
   reverse of the solution densities (4.6× more for conjugation) (§3.4, §5.4).
3. Odd D: σ-palindromic words land on the Lang image {β(x)⁻¹x} (proved, §2.8), so a tight balanced involution's Anti
   elements get ≈ √λ extra shots and its Anti penalty nearly vanishes (§3.5). So order 6 with a tight balanced
   involution beats order 3 at odd D (screens on five groups; unbalanced controls 18–36× worse) (§5.5).
4. Odd D also needs G's involutions in the rule, by stabiliser: one inside Fix(H) is missed at e^{−λ/(2|H|)}.
   With that term the rule predicts every odd-D screen's p1 to within 10 %. It explains PSL(2,25)²'s failure at
   (14,9) and the (15,9) anneal plateau (§4, §5.5).

## Open leads
- (16,9) on SL(2,8)²×Z703 (Z19×Z37, z ↦ 11z; swap∘conj with c of order 3): order 6, rule μ_A 10.2, +5.9 %, screened
  (runs/r2/ro169_sl8sq_703_k6.log). It is the best odd-D candidate: no involutions sit in Fix(α), Fix(α²). Needs about
  2.4·10⁴ evaluations at about 3 s each, so run 4 threads with CKPT. Command: ORBIT="6 2 1" OSUB=3 ASWAPC=1 AR=11
  OSTAB=1 THREADS=4 CKPT=... haar_order2 16 9 SECS SEED 8 OUT prod sl 8 sl 8 703.
- The low-μ odd-D records (11,9), (12,9), (14,9), (16,9) (μ = 14–16 at the record) look improvable by several per cent
  with order 3 alone, where group orders allow.
- Open questions: the annealer's preference for the isolated Frobenius class at (6,8); the 6-nat offset of the Poisson
  baseline at the extreme tail.

## Note for the coordinator
README lists (13,8) 6,999,552 as "finite geometry"; it is an order-6 orbit-symmetric Haar graph (orbit search).
