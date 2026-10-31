# sd5c-r1 cards ((13,5) above 11,700; see COMMON.md)

- c1 non-split metacyclic: <x, y | x^m = 1, y^k = x^s, y x y^-1 = x^r> (y^k in <x>, not 1), order m k >= 5851. New group kind in a copy of fsd.c.
- c2 C_p^2 : C_k with y acting by a non-scalar 2x2 matrix over F_p (diagonal diag(a,b), a != b, or a Jordan block), order p^2 k >= 5851. New kind.
- c3 metacyclic with EVEN m (C_m : C_k, m = 2^a m', y moving the odd primes; not in Opus's list) and m odd with some prime NOT moved (direct factors), with fsd meta as it is.
- c4 algorithm: clause-weighting / breakout energy in the tabu (copy of fsd.c); benchmark K = 13 on meta 61 90 12 1 (order 5,490, plain best 12) and meta 251 20 32 1 (5,020, plain solves in ~80 s): does it beat plain in the same time? Then try it on meta 61 96 21 1 (5,856).
- c5 algorithm: replace tabu by another local search (simulated annealing with a temperature schedule, or late-acceptance hill climbing) in a copy of fsd.c; same benchmark as c4.
- c6 Heisenberg-type groups: Heis(p) (order p^3, p = 3, 5, 7) x (C_m : C_k) or Heis(p) : C_k, order >= 5851. New kind. (The (9,5) 2,970 record was Heis(3) x (C11 : C5).)
- c7 wildcard: an approach none of the other cards uses (other cards: non-split metacyclic, C_p^2 : C_k matrix actions, even-m metacyclic, weighted tabu, annealing / LAHC, Heisenberg products, c8).
- c8 wildcard: an approach none of the other cards uses (other cards: non-split metacyclic, C_p^2 : C_k matrix actions, even-m metacyclic, weighted tabu, annealing / LAHC, Heisenberg products, c7).
