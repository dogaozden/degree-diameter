# s19 table: (19,9) random-symmetric-S cost by (group, ORBIT). Target: N > 658,863,336 (value 1,317,726,672 vertices).
# mu = N exp(-W/N) with W(19,9) = 1 + sum_{i=1..4} 19*18^(2i-1); mu from pick2.py.
# Row format: group | ORBIT | seed | header | RANDORB summary (samples, min, p10, median, mean, mu, time)
sl 457 x Z7 | ORBIT "3 6 1" | seed 1 | first test, RANDORB=4 stopped after 2 samples (costs 48, 38; 62 s, 57 s each) | samples=2 min=38 median=48 mean=43.00 mu=17.38
sl 457 x Z7 | ORBIT "3 5 4" | seed 2 | group sl 457 x Z_7, N=668104752 (2N=1336209504) | RANDORB d=19 D=9 group=sl 457 x Z_7 N=668104752 samples=1 min=60 p10=60 median=60 mean=60.00 mu=17.38 time=55.8
sl 457 x Z7 | ORBIT "3 4 7" | seed 2 | group sl 457 x Z_7, N=668104752 (2N=1336209504) | RANDORB d=19 D=9 group=sl 457 x Z_7 N=668104752 samples=1 min=246 p10=246 median=246 mean=246.00 mu=17.38 time=63.8
sl 457 x Z7 | ORBIT "3 6 1" | seed 2 | group sl 457 x Z_7, N=668104752 (2N=1336209504) | RANDORB d=19 D=9 group=sl 457 x Z_7 N=668104752 samples=1 min=28 p10=28 median=28 mean=28.00 mu=17.38 time=86.6
sl 419 x Z9 | ORBIT "3 6 1" | seed 2 | group sl 419 x Z_9, N=662036760 (2N=1324073520) | RANDORB d=19 D=9 group=sl 419 x Z_9 N=662036760 samples=1 min=50 p10=50 median=50 mean=50.00 mu=14.67 time=65.0
sl 877 x Z1 | ORBIT "3 6 1" | seed 2 | group sl 877 x Z_1, N=674525256 (2N=1349050512) | RANDORB d=19 D=9 group=sl 877 x Z_1 N=674525256 samples=1 min=66 p10=66 median=66 mean=66.00 mu=20.72 time=115.5
sl 877 x Z1 | ORBIT "3 6 1" | seed 2 | (correction: the run did finish one sample, the earlier NOT RUN line was wrong) | samples=1 min=66 median=66 mean=66.00 mu=20.72 time=115.5 s; memory 1.08 GB
# NOT RUN: sl 373 x Z13 (mu 20.8), sl 251 x Z42 (mu 15.6): stopped for the memory cap (see below).
#
# MEMORY: haar_big0 printed 0.60 GB (sl 419 x Z9), 0.63 GB (sl 457 x Z7), 1.08 GB (sl 877 x Z1) at N = 6.6-6.7e8,
# all above this card's 450 MB cap. Runs before I read the printed memory were above the cap; I stopped running after that.
#
# SUMMARY (1 sample per row unless noted; noisy; samples 55-115 s each under load, about 10x the quoted 2-15 s)
#   sl 457 x Z7 "3 6 1": 48, 38, 28 (3 samples, median 38, cost/mu 2.2)   <- lowest random-S cost at this N
#   sl 457 x Z7 "3 5 4": 60 (1 sample, cost/mu 3.4)
#   sl 457 x Z7 "3 4 7": 246 (1 sample): 6 random alpha-fixed generators are very bad
#   sl 419 x Z9 "3 6 1": 50 (cost/mu 3.4)
#   sl 877 x Z1 "3 6 1": 66 (cost/mu 3.2)
