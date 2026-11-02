import json
line = {"card": "h10", "cell": "3,10",
        "idea": "nlift non-abelian voltage lift on order-84/88 groups over 16 sampled 5+5 cubic bipartite bases; best Z7 x| Z12 (r=2, Z4 x F21) on base c5",
        "code": "research/squads/raise10/r4/h10/LOG.txt",
        "command": "TABU=1 THREADS=1 research/squads/raise10/r2/e13/nlift research/squads/raise10/r4/h10/grp/m7_12_2.bin research/squads/raise10/r4/h10/bases/c5.txt 10 75 4 research/squads/raise10/r4/h10/out/m7_12_2_c5 1.5 0.05 1200",
        "score": 0, "best_cost": 10, "valid": False,
        "check": "none (no cost-0 state); log research/squads/raise10/r4/h10/LOG.txt",
        "next": "Z7 x| Z12 (r=2) on base c5 stuck at cost 10 after 3 chains; run all 16 bases with more seeds and a longer tabu finisher"}
with open("/home/user/degree-diameter/research/squads/raise10/r4/scoreboard.jsonl", "a") as f:
    f.write(json.dumps(line) + "\n")
