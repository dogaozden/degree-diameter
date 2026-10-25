"""Rerun a random sample of bcd parts and compare the certificates line by line.

Usage: python3 bcd_spotcheck.py BCD MODE INPUT d D [--aut FILE] CERT0 CERT1 ... [--sample R] [--seed S] [--threads T]

Each CERT is a certificate (plain or .gz) of one part of the same check. R of them (default 2) are chosen at random,
the part i/K they claim is rerun with BCD on INPUT, and the new certificate must equal the old one exactly.
Prints one line per rerun part and "SPOTCHECK OK" or "SPOTCHECK FAIL". Use together with bcd_merge.py.
"""
import gzip
import os
import random
import subprocess
import sys
import tempfile


def read(path):
    op = gzip.open if path.endswith(".gz") else open
    with op(path, "rt") as f:
        return f.read()


def main():
    a = sys.argv[1:]
    opts = {"--sample": "2", "--seed": None, "--threads": "4", "--aut": None}
    for k in list(opts):
        if k in a:
            i = a.index(k)
            opts[k] = a[i + 1]
            del a[i:i + 2]
    if len(a) < 6:
        raise SystemExit(__doc__)
    bcd, mode, inp, d, D, certs = a[0], a[1], a[2], a[3], a[4], a[5:]
    rng = random.Random(opts["--seed"])
    pick = rng.sample(certs, min(int(opts["--sample"]), len(certs)))
    ok = True
    for c in pick:
        old = read(c)
        part = next(ln.split()[1:3] for ln in old.splitlines() if ln.startswith("part "))
        with tempfile.TemporaryDirectory() as td:
            new_path = os.path.join(td, "re.cert")
            cmd = [bcd, mode, inp, d, D, "--part", f"{part[0]}/{part[1]}", "--threads", opts["--threads"], "--cert", new_path]
            if opts["--aut"]:
                cmd += ["--aut", opts["--aut"]]
            subprocess.run(cmd, capture_output=True, text=True)
            new = open(new_path).read() if os.path.exists(new_path) else ""
        same = new == old
        ok &= same
        print(f"part {part[0]}/{part[1]} ({c}): {'identical' if same else 'DIFFERENT'}")
    print("SPOTCHECK OK" if ok else "SPOTCHECK FAIL")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
