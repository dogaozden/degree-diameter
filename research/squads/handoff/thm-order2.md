# Handoff: job thm-order2 (second session, branch claude/thm-order2-symmetry-wejgw7)

Main write-up: research/theorems/ORDER2.md (short answer first; ranked sections in §6). Files:
research/theorems/order2/ (§7 of ORDER2.md lists them). The first session's branch was
claude/thm-order2-symmetry-gap-4e2nmi; this branch carries both sessions (rebased on master, PR #312).

## State at the end of the second session

RUNS-STATE

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
   involution beats order 3 at odd D (screens on four groups; unbalanced controls 18–36× worse) (§5.5).

## Open leads
- (13,9) on SL(2,64)×Z133 (Z7×Z19, α³ fixing Z7 and negating Z19): order 6, rule μ_A 11.0 (record group 12.0),
  +2.9 %. Not started. Command pattern: runs/r2/launch_159.sh with `sl 64 133`, d = 13, ORBIT="6 2 1", and AR chosen
  of order 3 mod 7 and order 6 mod 19.
- The low-μ odd-D records (11,9), (12,9), (14,9), (16,9) (μ = 14–16 at the record) look improvable by several per cent
  with order 3 alone, where group orders allow.
- Open questions: the annealer's preference for the isolated Frobenius class at (6,8); the 6-nat offset of the Poisson
  baseline at the extreme tail.

## Note for the coordinator
README lists (13,8) 6,999,552 as "finite geometry"; it is an order-6 orbit-symmetric Haar graph (orbit search).
