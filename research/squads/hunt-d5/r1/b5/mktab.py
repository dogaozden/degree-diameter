import struct, sys, array
def dihedral(n):
    # elements i + n*j : r^i s^j, identity 0
    N=2*n; T=[0]*(N*N)
    for a in range(N):
        i1,j1=a%n,a//n
        for b in range(N):
            i2,j2=b%n,b//n
            i=(i1+(1 if j1==0 else -1)*i2)%n; j=(j1+j2)%2
            T[a*N+b]=i+n*j
    return N,T
def direct(A,B):
    (na,ta),(nb,tb)=A,B
    N=na*nb; T=[0]*(N*N)
    for x in range(N):
        xa,xb=divmod(x,nb)
        for y in range(N):
            ya,yb=divmod(y,nb)
            za=ta[xa*na+ya]; zb=tb[xb*nb+yb]
            T[x*N+y]=za*nb+zb
    return N,T
def write(name,NT):
    N,T=NT
    with open(name,'wb') as f:
        f.write(struct.pack('<i',N)); f.write(array.array('H',T).tobytes())
if __name__=="__main__":
    specs={'d636':(53,3),'d640':(16,10),'d644':(7,23),'d648':(27,6)}
    for name,(p,q) in specs.items():
        write(name+'.bin', direct(dihedral(p),dihedral(q)))
        print(name, 'written')
    