# w23 NOTES: order-2,500 groups P x| Z_4 (follows w15)

Start: 2026-11-01 01:31 UTC (card says work until 02:55 UTC). Last update: 01:41 UTC.

## Method
- Cost used everywhere (haar_tab convention, zero iff valid): |G \ T^{<=4}| + |G \ T'^{<=4}|, T = S^-1 S, T' = S S^-1,
  S = {e,a,b,c}. Checked against an independent BFS on the Haar graph (src/exh.c `check`, 300 random sets, 0 mismatches).
- src/aut.c: all automorphisms of a 2-generated table group (BFS tree + consistency check), orbits on G minus e.
- src/exh.c: exhaustive over S = {e,a,b,c}: a = one representative per Aut-orbit, b < c over all other elements.
  Each candidate costs about 10 microseconds (side-1 count stops early at the cap).

## u4m_7 (w15's best, P of order 625 x| Z_4, phi of order 2)
- Aut(G) order 20000, 14 orbits on G minus e (orbit sizes 1,1,4,4,20,20,50,100,100,100,200,400,400,1000).
- Central involution 1250 is an orbit of size 1. Element orders: 1x1, 2x1, 4x50, 5x624, 10x624, 20x1200. Centre 10.
- Haar cost floor by haar_tab (w15 and 60 s run here): 4.
- Exhaustive run in progress (see below).

## Next
- Exact floor for u4m_7, then far-pair analysis of the cost-4 sets (analyse.py), then the other P x| Z_4 tables.
