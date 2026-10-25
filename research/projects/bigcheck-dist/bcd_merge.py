"""Merge bcd certificates into one verdict.

Usage: python3 bcd_merge.py REPS.txt CERT1 CERT2 ... [--expect-input SHA256]

REPS.txt is the representative list written by `bcd ... --reps REPS.txt` (any part writes the same list). The merge
checks that:
  - every certificate is complete (ends with "end") and has the same header: version, mode, input and automorphism
    sha256, number of automorphisms, n, edges, degrees, bipartite flag, d, D, number of orbits and reps sha256;
  - the sha256 of REPS.txt equals reps_sha256 and the list has `orbits` entries;
  - the parts are 0..K-1 of the same K, each exactly once, with the ranges floor(iR/K) .. floor((i+1)R/K);
  - the src lines of part i are exactly REPS[lo:hi], in order;
  - every source has unreached 0 and ecc <= D.
Then diameter = max ecc, and the verdict is VALID iff also bipartite and maxdeg <= d.
"""
import hashlib
import sys

HEADER = ["version", "mode", "input_sha256", "aut_sha256", "nauts", "lift", "n", "edges", "mindeg", "maxdeg",
          "bipartite", "d", "D", "orbits", "reps_sha256"]


def read_cert(path):
    head, srcs, tail = {}, [], {}
    with open(path) as f:
        lines = [ln.rstrip("\n") for ln in f]
    if not lines or lines[0] != "bcd-cert 1":
        raise SystemExit(f"{path}: not a bcd certificate")
    if lines[-1] != "end":
        raise SystemExit(f"{path}: incomplete (no 'end' line)")
    for ln in lines[1:-1]:
        key, _, val = ln.partition(" ")
        if key == "src":
            t = val.split()
            if len(t) != 5 or t[1] != "ecc" or t[3] != "unreached":
                raise SystemExit(f"{path}: bad src line {ln!r}")
            srcs.append((int(t[0]), int(t[2]), int(t[4])))
        elif key == "part":
            head["part"] = tuple(int(x) for x in val.split())
        elif key in ("part_max_ecc", "part_unreached", "part_status"):
            tail[key] = val
        else:
            head[key] = val
    return head, srcs, tail


def main():
    args = sys.argv[1:]
    expect = None
    if "--expect-input" in args:
        i = args.index("--expect-input")
        expect = args[i + 1]
        del args[i:i + 2]
    if len(args) < 2:
        raise SystemExit(__doc__)
    reps_path, cert_paths = args[0], args[1:]
    raw = open(reps_path, "rb").read()
    reps = [int(x) for x in raw.split()]
    reps_sha = hashlib.sha256(raw).hexdigest()
    certs = [read_cert(p) for p in cert_paths]
    h0 = certs[0][0]
    for p, (h, _, _) in zip(cert_paths, certs):
        for k in HEADER:
            if h.get(k) != h0.get(k):
                raise SystemExit(f"{p}: header field {k} differs: {h.get(k)!r} vs {h0.get(k)!r}")
    if expect and h0["input_sha256"] != expect:
        raise SystemExit(f"input sha256 {h0['input_sha256']} != expected {expect}")
    R = int(h0["orbits"])
    if reps_sha != h0["reps_sha256"] or len(reps) != R:
        raise SystemExit("REPS file does not match the certificates (sha256 or length)")
    K = certs[0][0]["part"][1]
    seen = {}
    for p, (h, srcs, tail) in zip(cert_paths, certs):
        i, k, lo, hi = h["part"]
        if k != K:
            raise SystemExit(f"{p}: part count {k} != {K}")
        if i in seen:
            raise SystemExit(f"{p}: part {i} given twice ({seen[i]})")
        if (lo, hi) != (i * R // K, (i + 1) * R // K):
            raise SystemExit(f"{p}: part {i} has range {lo}..{hi}, expected {i * R // K}..{(i + 1) * R // K}")
        if [s[0] for s in srcs] != reps[lo:hi]:
            raise SystemExit(f"{p}: sources are not REPS[{lo}:{hi}]")
        seen[i] = p
    missing = [i for i in range(K) if i not in seen]
    if missing:
        raise SystemExit(f"missing parts: {missing[:20]}{' ...' if len(missing) > 20 else ''} ({len(missing)} of {K})")
    D, d = int(h0["D"]), int(h0["d"])
    all_srcs = [s for _, srcs, _ in certs for s in srcs]
    unreached = sum(s[2] for s in all_srcs)
    diam = max(s[1] for s in all_srcs)
    bad = [s for s in all_srcs if s[2] or s[1] > D]
    print(f"input sha256 {h0['input_sha256']} ({h0['mode']}), automorphisms sha256 {h0['aut_sha256']} ({h0['nauts']} generators)")
    print(f"n={h0['n']} edges={h0['edges']} degree min={h0['mindeg']} max={h0['maxdeg']} bipartite={h0['bipartite']}")
    print(f"{K} parts, {R} orbit representatives, all present once; max eccentricity {diam}, unreached {unreached}")
    if bad:
        print(f"{len(bad)} sources fail, e.g. {bad[:5]}")
    valid = not bad and h0["bipartite"] == "yes" and int(h0["maxdeg"]) <= d
    print(f"RESULT {'VALID' if valid else 'INVALID'} d={d} D={D} n={h0['n']}" + (f" diameter={diam}" if not unreached else ""))
    return 0 if valid else 1


if __name__ == "__main__":
    sys.exit(main())
