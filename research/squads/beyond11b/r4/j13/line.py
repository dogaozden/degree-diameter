import json
line = {
 "card": "j13",
 "idea": "even-D (5,12) products of two Frobenius groups Z_p x| Z_k (k even or odd allowed), plain random S (haar_gen3)",
 "code": "/home/user/degree-diameter/research/squads/beyond11b/bin/haar_gen3 (no new code); run log in /home/user/degree-diameter/research/squads/beyond11b/r4/j13/runs.txt",
 "command": "THREADS=1 timeout 105 nice -n 10 /home/user/degree-diameter/research/squads/beyond11b/bin/haar_gen3 5 12 95 14 4 D14.sol prod meta 71 10 14 meta 67 11 64 1",
 "cell": "(5,12)",
 "score": 0,
 "beats": "no",
 "valid": "none (no cost-0 S found; best cost 1 at (71x|10 14) x (67x|11 64), N=523270; a solution would beat 1,045,054)",
 "file": "none",
 "finding": "(5,12) products, N 522,660-523,270: (73x|4 27)x(199x|9 175) cost 2; (73x|6 9)x(199x|6 107) cost 104 (K=8); (97x|4 22)x(337x|4 148) cost 7973; (31x|6 26)x(281x|10 128) cost 17; (71x|10 14)x(67x|11 64) cost 1 (14k evals, seed 14 K=4), then cost 2 on 7 more seeds (K 4/8, 60-95 s). (6,12) (331x|6 300)x(337x|7 175) N=4,684,974 (would beat 9,366,240): cost 7 after 245 evals, slow.",
 "next": "Farm (71x|10 14)x(67x|11 64) with many more seeds; try pairs near N 523k with H order >= 50 (k = 10/11 factors) rather than k = 4/6 pairs."
}
print(json.dumps(line))
