# W(8) + one pair with the sigma of the 7,020 record (gq numbering)

Squad r3 card c4 reached structural cost 0 on W(7) + one pair (n = 401) with a 7-flag incident switch and the
random-like sigma of the 4,800 record. The r2 searches on W(8) all started from sigma = delta (the polarity) and stopped
at cost 2. This folder repeats c4's recipe on W(8): base gq_q8.bin numbering (w8_dm.in = W(8) with the sigma of the
7,020 solution, w8_dm.volt = its full Z6 voltages, z6lift cost 0), generator gen.py / scan.py copied from
research/squads/r3-d11D5/c4 (kind b = 8-flag incident switch, kind a = 9-flag switch, sigma(x*) = l*).
    python3 scan.py b 200 1      # starts/b_1_*.in, best 20 in top_b_1.json
    SECS=720 SEED=11 T0=20 T1=0.4 PF=0.3 PH=0.7 OUT=runs/r1.in OUT0=runs/r1_fail0.in ./po7 starts/b_1_96.in
