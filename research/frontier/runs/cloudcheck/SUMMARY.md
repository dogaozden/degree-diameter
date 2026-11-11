# cloudcheck: independent verification of new Haar records

Machine: 4 vCPU, 15 GB RAM (14 GB free at start), Linux 6.18. Each file's output, with a machine line and per-checker
exit code and peak RSS, is in the file of the same stem in this directory. Checker output is unedited.

Verdicts as printed by the checkers (`build_haar2.py` / `check_haar_indep.py`):

- d6D12_sl_71_13_orb3f0_s2 (Δ6·D12, 9,303,840 vertices): build_haar2.py `VALID`; check_haar_indep.py `RESULT VALID`
- d7D11_sl_43_67_orb3_s1 (Δ7·D11, 10,648,176 vertices): build_haar2.py `VALID`; check_haar_indep.py `RESULT VALID`
- d8D11_sl_89_31_orb3_s1 (Δ8·D11, 43,702,560 vertices): build_haar2.py `VALID`; check_haar_indep.py `RESULT VALID`
- d7D12_psl_163_13_orb3_s1 (Δ7·D12, 56,297,592 vertices): build_haar2.py `VALID`; check_haar_indep.py `RESULT VALID`
- d8D12_sl_163_31_orb3_s1 (Δ8·D12, 268,496,208 vertices): build_haar2.py `VALID` (peak RSS 12.9 GB, under a 13 GiB
  `ulimit -v` cap; completed); check_haar_indep.py `RESULT VALID`
