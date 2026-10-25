import json
row = {
    "card": "c7",
    "idea": "Level family (Z5 x Zk, zero hex levels) with random hexagon sub-voltages reproduces round-2 costs (k=2: 8, k=3: 100, k=4: 3699). Route analysis: 1-jump forward/backward routes give explicit voltages for levels +-1, +-2, but level 0 is the bottleneck (d(p,L) in {1,3} has one hex-only value there). No by-construction cover found beyond the D=7 level design (m=5).",
    "code": "/home/user/degree-diameter/research/squads/r2_d14D8/c7/mk_lev.py",
    "command": "cd /home/user/degree-diameter/research/squads/r2_d14D8/c7 && python3 -I mk_lev.py 5 5 1 1 1,2 zero rand same base_q5_m5.txt && /home/user/degree-diameter/research/squads/cells/d14D8_work/lifteval base_q5_m5.txt 8 all",
    "best": {"q5": 5, "q7": 5, "q11": 5},
    "dgq": {"q5": 25, "q7": 30, "q11": 40},
    "valid": True,
    "next": "Cover level 0 by construction: give d(p,L) in {1,3} pairs 2-jump differences c(x)-c(x') that are distinct on each pencil-to-line class, then test k=5 at q=5.",
}
with open("/home/user/degree-diameter/research/squads/r2_d14D8/scoreboard.jsonl", "a") as f:
    f.write(json.dumps(row) + "\n")
print("appended")
