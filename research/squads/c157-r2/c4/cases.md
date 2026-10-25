| case | q | K | k | kind | maxdeg (Delta) | kcopy: max ecc, bad src -> verdict | apsp: diameter -> verdict | apsp_sym: diameter -> verdict | all three agree | lemma (ecc<=7 iff diam<=7) |
|---|---|---|---|---|---|---|---|---|---|---|
| q3_K1_cm_k1 | 3 | 1 | 1 | cm | 5 (5) | 7, 0 -> OK | 7 -> VALID | 7 -> VALID | yes | yes |
| q3_K1_cm_k2 | 3 | 1 | 2 | cm | 6 (6) | 7, 0 -> OK | 7 -> VALID | 7 -> VALID | yes | yes |
| q3_K1_cm_k3 | 3 | 1 | 3 | cm | 8 (7) | 7, 0 -> FAIL | 7 -> INVALID | 7 -> INVALID | yes | yes |
| q3_K1_done_k1 | 3 | 1 | 1 | done | 5 (5) | 7, 0 -> OK | 7 -> VALID | 7 -> VALID | yes | yes |
| q3_K1_done_k2 | 3 | 1 | 2 | done | 6 (6) | 7, 0 -> OK | 7 -> VALID | 7 -> VALID | yes | yes |
| q3_K1_done_k3 | 3 | 1 | 3 | done | 8 (7) | 7, 0 -> FAIL | 7 -> INVALID | 7 -> INVALID | yes | yes |
| q3_K1_nohub_k1 | 3 | 1 | 1 | nohub | 5 (5) | 7, 0 -> OK | 7 -> VALID | 7 -> VALID | yes | yes |
| q3_K1_nohub_k2 | 3 | 1 | 2 | nohub | 6 (6) | 7, 0 -> OK | 7 -> VALID | 7 -> VALID | yes | yes |
| q3_K1_nohub_k3 | 3 | 1 | 3 | nohub | 7 (7) | 7, 0 -> OK | 7 -> VALID | 7 -> VALID | yes | yes |
| q3_K1_swap_k1 | 3 | 1 | 1 | swap | 5 (5) | 8, 1 -> FAIL | 8 -> INVALID | 8 -> INVALID | yes | yes |
| q3_K1_swap_k2 | 3 | 1 | 2 | swap | 6 (6) | 7, 0 -> OK | 7 -> VALID | 7 -> VALID | yes | yes |
| q3_K1_swap_k3 | 3 | 1 | 3 | swap | 8 (7) | 7, 0 -> FAIL | 7 -> INVALID | 7 -> INVALID | yes | yes |
| q3_K2_cm_k1 | 3 | 2 | 1 | cm | 5 (5) | 7, 0 -> OK | 7 -> VALID | 7 -> VALID | yes | yes |
| q3_K2_cm_k2 | 3 | 2 | 2 | cm | 7 (6) | 7, 0 -> FAIL | 7 -> INVALID | 7 -> INVALID | yes | yes |
| q3_K2_cm_k3 | 3 | 2 | 3 | cm | 9 (7) | 7, 0 -> FAIL | 7 -> INVALID | 7 -> INVALID | yes | yes |
| q3_K2_done_k1 | 3 | 2 | 1 | done | 5 (5) | 7, 0 -> OK | 7 -> VALID | 7 -> VALID | yes | yes |
| q3_K2_done_k2 | 3 | 2 | 2 | done | 7 (6) | 7, 0 -> FAIL | 7 -> INVALID | 7 -> INVALID | yes | yes |
| q3_K2_done_k3 | 3 | 2 | 3 | done | 9 (7) | 7, 0 -> FAIL | 7 -> INVALID | 7 -> INVALID | yes | yes |
| q3_K2_nohub_k1 | 3 | 2 | 1 | nohub | 5 (5) | 8, 2 -> FAIL | 8 -> INVALID | 8 -> INVALID | yes | yes |
| q3_K2_nohub_k2 | 3 | 2 | 2 | nohub | 6 (6) | 8, 4 -> FAIL | 8 -> INVALID | 8 -> INVALID | yes | yes |
| q3_K2_nohub_k3 | 3 | 2 | 3 | nohub | 7 (7) | 8, 6 -> FAIL | 8 -> INVALID | 8 -> INVALID | yes | yes |
| q3_K2_swap_k1 | 3 | 2 | 1 | swap | 5 (5) | 8, 1 -> FAIL | 8 -> INVALID | 8 -> INVALID | yes | yes |
| q3_K2_swap_k2 | 3 | 2 | 2 | swap | 7 (6) | 8, 1 -> FAIL | 8 -> INVALID | 8 -> INVALID | yes | yes |
| q3_K2_swap_k3 | 3 | 2 | 3 | swap | 9 (7) | 8, 1 -> FAIL | 8 -> INVALID | 8 -> INVALID | yes | yes |
| q3_K3_cm_k1 | 3 | 3 | 1 | cm | 6 (5) | 7, 0 -> FAIL | 7 -> INVALID | 7 -> INVALID | yes | yes |
| q3_K3_cm_k2 | 3 | 3 | 2 | cm | 8 (6) | 7, 0 -> FAIL | 7 -> INVALID | 7 -> INVALID | yes | yes |
| q3_K3_cm_k3 | 3 | 3 | 3 | cm | 10 (7) | 7, 0 -> FAIL | 7 -> INVALID | 7 -> INVALID | yes | yes |
| q3_K3_done_k1 | 3 | 3 | 1 | done | 6 (5) | 7, 0 -> FAIL | 7 -> INVALID | 7 -> INVALID | yes | yes |
| q3_K3_done_k2 | 3 | 3 | 2 | done | 8 (6) | 7, 0 -> FAIL | 7 -> INVALID | 7 -> INVALID | yes | yes |
| q3_K3_done_k3 | 3 | 3 | 3 | done | 10 (7) | 7, 0 -> FAIL | 7 -> INVALID | 7 -> INVALID | yes | yes |
| q3_K3_nohub_k1 | 3 | 3 | 1 | nohub | 5 (5) | 8, 5 -> FAIL | 8 -> INVALID | 8 -> INVALID | yes | yes |
| q3_K3_nohub_k2 | 3 | 3 | 2 | nohub | 6 (6) | 8, 10 -> FAIL | 8 -> INVALID | 8 -> INVALID | yes | yes |
| q3_K3_nohub_k3 | 3 | 3 | 3 | nohub | 7 (7) | 8, 15 -> FAIL | 8 -> INVALID | 8 -> INVALID | yes | yes |
| q3_K3_swap_k1 | 3 | 3 | 1 | swap | 6 (5) | 7, 0 -> FAIL | 7 -> INVALID | 7 -> INVALID | yes | yes |
| q3_K3_swap_k2 | 3 | 3 | 2 | swap | 8 (6) | 7, 0 -> FAIL | 7 -> INVALID | 7 -> INVALID | yes | yes |
| q3_K3_swap_k3 | 3 | 3 | 3 | swap | 10 (7) | 7, 0 -> FAIL | 7 -> INVALID | 7 -> INVALID | yes | yes |
| q5_K2_cm_k1 | 5 | 2 | 1 | cm | 7 (7) | 7, 0 -> OK | 7 -> VALID | 7 -> VALID | yes | yes |
| q5_K2_cm_k2 | 5 | 2 | 2 | cm | 8 (8) | 7, 0 -> OK | 7 -> VALID | 7 -> VALID | yes | yes |
| q5_K2_cm_k3 | 5 | 2 | 3 | cm | 9 (9) | 7, 0 -> OK | 7 -> VALID | 7 -> VALID | yes | yes |
| q5_K2_cmB_k1 | 5 | 2 | 1 | cmB | 7 (7) | 7, 0 -> OK | 7 -> VALID | 7 -> VALID | yes | yes |
| q5_K2_cmB_k2 | 5 | 2 | 2 | cmB | 8 (8) | 7, 0 -> OK | 7 -> VALID | 7 -> VALID | yes | yes |
| q5_K2_cmB_k3 | 5 | 2 | 3 | cmB | 9 (9) | 7, 0 -> OK | 7 -> VALID | 7 -> VALID | yes | yes |
| q5_K2_nohub_k1 | 5 | 2 | 1 | nohub | 7 (7) | 8, 2 -> FAIL | 8 -> INVALID | 8 -> INVALID | yes | yes |
| q5_K2_nohub_k2 | 5 | 2 | 2 | nohub | 8 (8) | 8, 4 -> FAIL | 8 -> INVALID | 8 -> INVALID | yes | yes |
| q5_K2_nohub_k3 | 5 | 2 | 3 | nohub | 9 (9) | 8, 6 -> FAIL | 8 -> INVALID | 8 -> INVALID | yes | yes |
| q5_K2_swap_k1 | 5 | 2 | 1 | swap | 7 (7) | 7, 0 -> OK | 7 -> VALID | 7 -> VALID | yes | yes |
| q5_K2_swap_k2 | 5 | 2 | 2 | swap | 8 (8) | 7, 0 -> OK | 7 -> VALID | 7 -> VALID | yes | yes |
| q5_K2_swap_k3 | 5 | 2 | 3 | swap | 9 (9) | 7, 0 -> OK | 7 -> VALID | 7 -> VALID | yes | yes |
| q5_K4_cm_k1 | 5 | 4 | 1 | cm | 7 (7) | 7, 0 -> OK | 7 -> VALID | 7 -> VALID | yes | yes |
| q5_K4_cm_k2 | 5 | 4 | 2 | cm | 9 (8) | 7, 0 -> FAIL | 7 -> INVALID | 7 -> INVALID | yes | yes |
| q5_K4_cm_k3 | 5 | 4 | 3 | cm | 11 (9) | 7, 0 -> FAIL | 7 -> INVALID | 7 -> INVALID | yes | yes |
| q5_K4_done_k1 | 5 | 4 | 1 | done | 7 (7) | 7, 0 -> OK | 7 -> VALID | 7 -> VALID | yes | yes |
| q5_K4_done_k2 | 5 | 4 | 2 | done | 9 (8) | 7, 0 -> FAIL | 7 -> INVALID | 7 -> INVALID | yes | yes |
| q5_K4_done_k3 | 5 | 4 | 3 | done | 11 (9) | 7, 0 -> FAIL | 7 -> INVALID | 7 -> INVALID | yes | yes |
| q5_K4_nohub_k1 | 5 | 4 | 1 | nohub | 7 (7) | 8, 12 -> FAIL | 8 -> INVALID | 8 -> INVALID | yes | yes |
| q5_K4_nohub_k2 | 5 | 4 | 2 | nohub | 8 (8) | 8, 20 -> FAIL | 8 -> INVALID | 8 -> INVALID | yes | yes |
| q5_K4_nohub_k3 | 5 | 4 | 3 | nohub | 9 (9) | 8, 28 -> FAIL | 8 -> INVALID | 8 -> INVALID | yes | yes |
| q5_K4_swap_k1 | 5 | 4 | 1 | swap | 7 (7) | 7, 0 -> OK | 7 -> VALID | 7 -> VALID | yes | yes |
| q5_K4_swap_k2 | 5 | 4 | 2 | swap | 9 (8) | 7, 0 -> FAIL | 7 -> INVALID | 7 -> INVALID | yes | yes |
| q5_K4_swap_k3 | 5 | 4 | 3 | swap | 11 (9) | 7, 0 -> FAIL | 7 -> INVALID | 7 -> INVALID | yes | yes |
| q5_K8_cm_k1 | 5 | 8 | 1 | cm | 11 (7) | 8, 10 -> FAIL | 8 -> INVALID | 8 -> INVALID | yes | yes |
| q5_K8_cm_k2 | 5 | 8 | 2 | cm | 13 (8) | 8, 9 -> FAIL | 8 -> INVALID | 8 -> INVALID | yes | yes |
| q5_K8_cm_k3 | 5 | 8 | 3 | cm | 15 (9) | 8, 9 -> FAIL | 8 -> INVALID | 8 -> INVALID | yes | yes |
| q5_K8_done_k1 | 5 | 8 | 1 | done | 11 (7) | 7, 0 -> FAIL | 7 -> INVALID | 7 -> INVALID | yes | yes |
| q5_K8_done_k2 | 5 | 8 | 2 | done | 13 (8) | 7, 0 -> FAIL | 7 -> INVALID | 7 -> INVALID | yes | yes |
| q5_K8_done_k3 | 5 | 8 | 3 | done | 15 (9) | 7, 0 -> FAIL | 7 -> INVALID | 7 -> INVALID | yes | yes |
| q5_K8_nohub_k1 | 5 | 8 | 1 | nohub | 7 (7) | 8, 29 -> FAIL | 8 -> INVALID | 8 -> INVALID | yes | yes |
| q5_K8_nohub_k2 | 5 | 8 | 2 | nohub | 8 (8) | 8, 44 -> FAIL | 8 -> INVALID | 8 -> INVALID | yes | yes |
| q5_K8_nohub_k3 | 5 | 8 | 3 | nohub | 9 (9) | 8, 60 -> FAIL | 8 -> INVALID | 8 -> INVALID | yes | yes |
| q5_K8_swap_k1 | 5 | 8 | 1 | swap | 11 (7) | 8, 11 -> FAIL | 8 -> INVALID | 8 -> INVALID | yes | yes |
| q5_K8_swap_k2 | 5 | 8 | 2 | swap | 13 (8) | 8, 10 -> FAIL | 8 -> INVALID | 8 -> INVALID | yes | yes |
| q5_K8_swap_k3 | 5 | 8 | 3 | swap | 15 (9) | 8, 10 -> FAIL | 8 -> INVALID | 8 -> INVALID | yes | yes |

Notes (c4, 2026-10-24). Rows: q in {3,5}; K = freed flags; k = copies parameter (2k+1 copies); kind: cm = cover_match output,
done = d7hexr output (SKIPFULL, claims freed sources OK), cmB = cover_match with another seed, nohub = hub-graph edges removed
("hubedges 0"), swap = two random transpositions of M (still a bijection). Delta = q+1+k; hubs have degree (2k+1) + hub-graph degree.
All three checkers read the same edge list written by kcopy_hub edges, so the agreement tests the BFS/lemma side, not the builder.
Totals: 72 cases, all three agree in 72/72, lemma (ecc<=7 iff diam<=7) holds in 72/72, max freed/hub ecc equals the diameter in every row.
Verdicts: 22 VALID, 50 INVALID. Of the INVALID rows, 25 fail only on the degree bound (ecc and diam both <= 7) and 25 fail on distance.
