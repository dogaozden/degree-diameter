import json
rec = {
 "card": "f07", "cell": "(6,11)",
 "idea": "fresh random-orbit seeds on PSL(2,37) x Z43 with ORBIT 3 2 0, 95 s each",
 "group": "psl 37 43", "N": 1088244, "best_cost": 3, "vertices_if_solved": 0, "beats_record": False,
 "file": "/home/user/degree-diameter/research/squads/raise11/r3/f07/run_37_43_7204.out.best",
 "command": "ORBIT=3 2 0 THREADS=1 timeout 105 nice -n 10 /home/user/degree-diameter/research/squads/raise11/bin/haar_big0 6 11 95 <seed> 4 <out> psl 37 43",
 "evals": 73383,
 "finding": "15 fresh seeds 7200-7214: final costs 3,4,4,5,6,6,8,8,8,9,9,9,10,11,12 (median 8), no cost<=2 state so no resume; ~4.6k evals per 95 s run",
 "next": "more fresh seeds, or the card's next rung psl 31 73 (N 1,086,240)"
}
with open("/home/user/degree-diameter/research/squads/raise11/r3/scoreboard.jsonl", "a") as f:
    f.write(json.dumps(rec) + "\n")
print("ok")
