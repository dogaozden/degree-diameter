import math
def W(d, D):
    if D % 2 == 0: return sum(d * (d - 1) ** (2 * i) for i in range(D // 2))
    return 1 + sum(d * (d - 1) ** (2 * i - 1) for i in range(1, (D - 1) // 2 + 1))
def mu(N, d, D):
    return N * math.exp(-W(d, D) / N)
def lnC_rand(N, d):   # S = {e} + (d-1) free elements, unordered
    return (d - 1) * math.log(N) - math.lgamma(d)
def lnC_orb(N, d, f, m, fix=35):  # f in {0,1,2} as in ORBIT="k m f"; e is one fixed slot when f>=1
    nfix = max(f - 1, 0)
    return m * math.log(N / 3) + nfix * math.log(fix) - math.lgamma(m + 1)
if __name__ == "__main__":
    import sys
    # stats lines: (label, d, D, N, form, min, median, mu_reported)
    rows = [
      ("sl37xZ397 random",6,13,20094552,"rand",202,254,5.10),
      ("sl37xZ397 orbit 3 2 0",6,13,20094552,"orb",198,1266,5.10),
      ("meta1079011x19 random",6,13,20501209,"rand",100,260,7.03),
      ("meta1079011x19 orbit 3 2 0",6,13,20501209,"orb",16493304,16880690,7.03),
      ("sl113x1 random",5,13,1442784,"rand",0,36,0.27),
      ("psl79x7 random",5,13,1725360,"rand",3,79,4.04),
      ("psl67x13 random",5,13,1954524,"rand",24881,112047,20.92),
      ("sl29x97 random",5,13,2362920,"rand",11130,25104,182.81),
    ]
    for lab,d,D,N,form,mn,med,mr in rows:
        m_ = mu(N,d,D)
        print(f"{lab:28s} N={N:>10d} W/N={W(d,D)/N:6.2f} mu={m_:8.3f} (reported {mr}) min={mn} median={med}")
