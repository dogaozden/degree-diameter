# k = 11 monolithic runs (stopped at session end, 2026-10-25 ~14:55 UTC, no answer)

CNF: `enc_quot.py 11 q3_k11.cnf --sym --nf2 --ntt --alltr`, sha256 b6101044dbd9641a5a35d44fa374667ce0288792c06b38e301e8ea2a40767525
(header: p cnf 784395 2723679; A-only).

| solver | CPU time when stopped | result |
|---|---|---|
| kissat (default) | 8.1 h | none |
| CaDiCaL --lrat streamed into lrat-check (stream_cert.sh) | 6.9 h | none (the checker kept up the whole time) |
| kissat, A-only, weaker symmetry breaking (q2) | 3.0 h (stopped earlier) | none |
| kissat on the signed instance (qs2, qs3) | about 1 h + 3 h | none |
