# Per-cell plans for gen.py (exec'd with NM = nearmiss.json and PLANS to fill).
# plan entry: (label, group-builder expression, start set S0 (indices) or None, time share)
# Group orders must EXCEED record/2:  d6: > 342 (table 684)   d10: > 2000 (table 4000).
# Fallbacks: d6 order 330 (660 vertices), d10 order 1791 = Z_199 x| Z_9 (3582 vertices).
# Valid-fallback S were found by the C annealers and are re-checked with lib.is_valid at run time.

PLANS["d6_nearmiss"] = dict(
    cell="d6D5", d=6,
    blurb="Near-miss reconstruction: the 2-short Haar graphs of orders 351 and 355 (metacyclic) and a 4-short one of order 360 (SL(2,5) x Z_3), "
          "scan of all single swaps, then annealing from the near miss with perturbed restarts.",
    plan=[("meta 117/3/16, order 351, 2 short", "group_meta(117, 3, 16)", NM["d6_meta_117_3_16"]["S"], 4),
          ("meta 71/5/5, order 355, 2 short", "group_meta(71, 5, 5)", NM["d6_meta_71_5_5"]["S"], 4),
          ("SL(2,5) x Z_3, order 360, 4 short", "group_times_cyclic(group_sl2(5), 3)", NM.get("d6_sl5_z3", {}).get("S"), 3)],
    fallback=("group_meta(33, 10, 26)", [0, 179, 116, 180, 47, 306]),     # order 330 -> 660 vertices, valid
)

PLANS["d6_family"] = dict(
    cell="d6D5", d=6,
    blurb="Other group families just above the threshold 342: Heisenberg(3) x Z_13 (351), Heisenberg(7) (343), "
          "AGL(1,9) x Z_5 (360), AGL(1,5) x Z_18 (360); annealing from random S.",
    plan=[("Heis(3) x Z_13, order 351", "group_times_cyclic(group_heis(3), 13)", None, 3),
          ("Heis(7), order 343", "group_heis(7)", None, 2),
          ("AGL(1,9) x Z_5, order 360", "group_times_cyclic(group_agl(9), 5)", None, 2),
          ("AGL(1,5) x Z_18, order 360", "group_times_cyclic(group_agl(5), 18)", None, 2)],
    fallback=("group_meta(33, 10, 26)", [0, 179, 116, 180, 47, 306]),
)

PLANS["d10_nearmiss"] = dict(
    cell="d10D5", d=10,
    blurb="Near-miss reconstruction: Z_401 x| Z_5 (order 2005, 6 short), scan of all single swaps, then annealing from "
          "the near miss with perturbed restarts; Z_336 x| Z_6 (2016) from random S as a second group.",
    plan=[("meta 401/5/39, order 2005, 6 short", "group_meta(401, 5, 39)", NM["d10_meta_401_5_39"]["S"], 5),
          ("meta 336/6/17, order 2016", "group_meta(336, 6, 17)", None, 1)],
    fallback=("group_meta(199, 9, 180)", [0, 1754, 312, 1155, 1465, 922, 1459, 1712, 704, 1314]),
)

PLANS["d10_family"] = dict(
    cell="d10D5", d=10,
    blurb="Other group families just above the threshold 2000: SL(2,7) x Z_6 (2016), Heisenberg(7) x Z_6 (2058), "
          "AGL(1,13) x Z_13 (2028), AGL(1,16) x Z_9 (2160); annealing from random S.",
    plan=[("SL(2,7) x Z_6, order 2016", "group_times_cyclic(group_sl2(7), 6)", None, 2),
          ("Heis(7) x Z_6, order 2058", "group_times_cyclic(group_heis(7), 6)", None, 2),
          ("AGL(1,13) x Z_13, order 2028", "group_times_cyclic(group_agl(13), 13)", None, 1),
          ("AGL(1,16) x Z_9, order 2160", "group_times_cyclic(group_agl(16), 9)", None, 1)],
    fallback=("group_meta(199, 9, 180)", [0, 1754, 312, 1155, 1465, 922, 1459, 1712, 704, 1314]),
)
