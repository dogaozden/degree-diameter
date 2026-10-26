import json, sys
recs = [json.loads(l) for l in open('/home/user/degree-diameter/research/squads/beyond/r1/c16/records_merged.jsonl')]
def best(Dl, Dh, Dcap):
    # best order over records with dmax<=Dl and diameter<=Dcap
    c = [r for r in recs if r['dmax'] <= Dl and r['D'] <= Dcap]
    return max(c, key=lambda r: r['order']) if c else None
# header values where known (Delta, D) -> value to beat
hdr = {(17,5):33792,(18,5):42840,(19,5):52428,(20,5):62640,(17,7):5631276,(18,7):7240212,(19,7):11184810,(20,7):15658734,
       (17,8):36201060,(17,9):337394400,(17,10):4708566360}
mb = lambda D,d: 2*sum((d-1)**i for i in range(D)) - (6 if D not in (3,4,6) else 0)
for Dl in list(range(3,21)):
    pass
print('Delta D  best_order building I J dA dB diam  | bound(M_b-6 side*2)  ratio_to_bound')
for Dl in range(17,21):
    for D in range(3,11):
        b = best(Dl, None, D)
        bound = mb(D, Dl)
        if b is None:
            print(Dl, D, 'none'); continue
        print(Dl, D, b['order'], b['building'], b['I'], b['J'], b['dA'], b['dB'], b['D'], '|', bound, round(b['order']/bound,4), 'hdr', hdr.get((Dl,D)))
print('--- D=11,12 at Delta 3..10')
for Dl in range(3,11):
    for D in (11,12):
        b = best(Dl, None, D)
        bound = mb(D, Dl)
        if b is None: print(Dl, D, 'none'); continue
        print(Dl, D, b['order'], b['building'], b['I'], b['J'], b['dA'], b['dB'], b['D'], '|', bound, round(b['order']/bound,6))
