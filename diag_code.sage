# Practical tests for our attacks on "Simultaneous Diagonalization of Incomplete Matrices"
 
# 1. Algorithms for Problems C and D
 
#The following are intermediate functions for matching list indices
 
#A function gives the natural list index associated to pairs (a,b) in I
#where I=[(a,b) for a in range(t) for b in range(t) if a<b]
def pos(a,b,t):
    return a*t-a*(a+1)/2+(b-a)-1
 
#where I=[(a,b) for a in range(t) for b in range(t) if a!=b]
def x(a,b):          
    if b<=a-1:
        return b
    if b>=a+1:
        return b-1
 
def tau(a,b,t):        
    return a*(t-1)+x(a,b)
 
#where I=[(a,b) for a in range(t) for b in range(t)]
def y(a,b,t):
    if a==0:
        return b
    else:
        return a*(t-1)+(b+a)
 
def leftinv(A):
    return (A.T*A).inverse()*A.T
 
def rightinv(A):
    return A.T*(A*A.T).inverse()
 
def modNear(a,b):
    res=a%b
    if res>b/2:
        return res-b
    return res
 
#Algorithm for PROBLEM C
 
#input: V is a pxn matrix and a finite list of pxn matrces W_a
#The linear algebra is done over F_prime for speed up, and we define the matrices over F_prime
def SOLVE_C(V,listW,n,p,prime):                                                                                                                                                        
    t=len(listW)
    r=n-p
    E=V.right_kernel().basis_matrix()  
    Vp=rightinv(V) 
    B=t*(t-1)/2
    I=[(a,b) for a in range(t) for b in range(t) if a<b]
     
    #define the matrices Delta_ab
    Delab=[matrix(GF(prime),listW[a]*Vp*listW[b]-listW[b]*Vp*listW[a]) for (a,b) in I]
   
    #we solve the system of linear equations in F_prime
    #define a matrix Delta by stacking each Delta_ab below each other
    Delta=Delab[0]
    for i in range(B-1):
        Delta=Delta.stack(Delab[i+1])
   
    #define matrix W
    W=matrix(GF(prime),B*p,t*r)
    for (a,b) in I:
        for k in range(B):
            if k==pos(a,b,t):   #blocks W_b | W_-a in pos a,b
                W[k*p:(k+1)*p,a*r:(a+1)*r]=matrix(GF(prime),listW[b]*E.T)
                W[k*p:(k+1)*p,b*r:(b+1)*r]=matrix(GF(prime),-listW[a]*E.T)
 
    #Solution to the system of linear equations
    X=leftinv(W)*Delta
    X_blocks=[X[a*r:(a+1)*r,:] for a in range(t)]
    Y=[Vp*listW[a] for a in range(t)]
   
    #define matrices Z_a
    Z=[Y[a]+matrix(GF(prime),E).T*X_blocks[a] for a in range(t)]
    return [Z[a].eigenvalues() for a in range(t)]
 
#To test Algoritm A_C we define a function test_Algorithm_C which generates random instances for Problem C and uses SOLVE_C to solve them
#input: parameters n,p,t and a prime number 'prime' to compute over F_prime
def test_Algorithm_C(n,p,t,prime):  
    print '(n,p,t)',(n,p,t)      
    print 'theoretical bound p = ceil(sqrt(2*n))',ceil(sqrt(2*n))
    print 'theoretical bound t = ceil(sqrt(2*n)-1)',ceil(sqrt(2*n)-1)  
 
    #create random instance for Problem C
    P=random_matrix(GF(prime),p,n)
    Q=random_matrix(GF(prime),n,n)                                            
                                                             
    print 'rank of P',(P.rank(),p)
    print 'rank of Q',(Q.rank(),n)
    if (Q.rank()!=n):
        print 'the matrix Q is not invertible!'
 
    V=P*Q                                                                  
    print 'rank of V',(V.parent(),V.rank(),p)  
 
    u=[]                                                                    
    U=[]                                  
    listW=[]                                    
    for a in range(t):
        u.append(random_vector(GF(prime),n))                                    
        U.append(diagonal_matrix(GF(prime),u[a]))                              
        listW.append(P*U[a]*Q)                                              
 
    time0=cputime()
    S=SOLVE_C(V,listW,n,p,prime)
    runtime=cputime()-time0
 
    original=[sorted(u[a]) for a in range(t)]
    found=[sorted(S[a]) for a in range(t)]
   
    print 'Solution',original==found
    print 'runtime',runtime
 
#Algorithm for PROBLEM D
 
#input: V is a pxp matrix and a finite list of pxp matrces W_a
#The linear algebra is done over F_prime for speed up, and we define the matrices over F_prime
def SOLVE_D(V,listW,n,p,prime):                                                              
    r=n-p  
    t=len(listW)                                                       
   
    J=[(a,b) for a in range(t) for b in range(t) if a!=b]                                                
   
    #define the matrices Delta_ab  
    D=[matrix(GF(prime),listW[a]*V.inverse()*listW[b]-listW[b]*V.inverse()*listW[a]) for (a,b) in J]                                            
 
    #compute the intersections of the images of the matrices Delta_ab
    Cap=[]
    Init=[D[tau(0,1,t)].column_space()]+[D[tau(a,0,t)].column_space() for a in [1..t-1]]
    for a in range(t):
        c=Init[a]
        for b in [b for b in range(t) if b != a]:
            c=c.intersection(D[tau(a,b,t)].column_space())
        Cap.append(c)
 
    #Define the matrices Ca for a in range(t)
    C=[c.basis_matrix().T for c in Cap]
    rkCa=C[0].rank()
    #Find matrices N^(a,b)=(N_ab | N_ba).T
    #first we define the matrices C_ab=(Ca|-Cb)
    matCab=[C[a].augment(-C[b]) for (a,b) in J]
 
    #Define the matrices N^(a,b)
    matN=[(C[a].augment(-C[b])).solve_right(D[tau(a,b,t)]) for (a,b) in J]
   
    Nab=[N[0:rkCa,:] for N in matN]
    Nba=[N[rkCa:2*rkCa,:] for N in matN]
 
    #The matrix BigN is used to solve the system of linear equations
    BigN=matrix(GF(prime),t*(rkCa+p),(t-1)*t*p)
    for (a,b) in J:
        u1=tau(a,b,t)
        u2=t*rkCa
        BigN[a*rkCa:(a+1)*rkCa,u1*p:(u1+1)*p]=Nab[u1]
        BigN[u2+b*p:u2+(b+1)*p,u1*p:(u1+1)*p]=-matrix.identity(p)
    kerN=BigN.left_kernel()
    #The matrices Ma.inverse() are the first t rxr blocks of the left-kernel
    #The list matM contains the matrices Ma for a in range(t)
    matM=[kerN.basis_matrix()[:,a*rkCa:(a+1)*rkCa].inverse() for a in range(t)]  
   
    #Deduce the matrices Va by computing Va=Ca*Ma
    matV=[C[a]*matM[a] for a in range(t)]
   
    #Compute the augmented matrices of matrices V and Wa for a=1,..,t
    Vnew=Matrix(GF(prime),p,p+r)
    Vnew[:,0:p]=V
    listWnew=[listW[a].augment(matV[a]) for a in range(t)]
 
    #Compute the eigenvalues by running Algorithm SOLVE1 on augmented matrices
    S=SOLVE_C(Vnew,listWnew,n,p,prime)
    return S
 
#To test Algoritm A_D we define a function test_Algorithm_D which generates random instances for Problem D and uses SOLVE1 to solve them
#input: parameters n,p,q,t and a prime number 'prime' to compute over F_prime
def test_Algorithm_D(n,p,t,prime):                                                                                                        
    print '(n,p,t)',(n,p,t)      
    print 'ratio p/n',((p/n).n(),(2/3).n())
   
    #create random instance for Problem D
    P=random_matrix(GF(prime),p,n)
    Q=random_matrix(GF(prime),n,p)                                            
                                                             
    print 'rank of P',(P.rank(),p)
    print 'rank of Q',(Q.rank(),p)                                        
    V=P*Q                                                                  
    print 'rank of V',(V.parent(),V.rank(),p)                                        
    u=[]                                                                    
    U=[]                                        
    listW=[]                                  
    for a in range(t):
        u.append(random_vector(GF(prime),n))                                    
        U.append(diagonal_matrix(GF(prime),u[a]))                              
        listW.append(P*U[a]*Q)                                                                                                      
       
    time0=cputime()
    S=SOLVE_D(V,listW,n,p,prime)
    runtime=cputime()-time0
 
    original=[sorted(u[a]) for a in range(t)]
    found=[sorted(S[a]) for a in range(t)]
    print 'Solution',original==found
    print 'running time',runtime
     
#2. Applications in cryptanalysis                                      
#Application 1: multi-prime CRT-ACD Problem
 
#input: n (the number of prime factors),p,t,eta (the bit-size of prime factors of M), rho (the bit-size of the CRT-errors), prime (a prime number to speed up by computing over F_prime)
def improve_crtacd(n,p,t,eta,rho,prime):
    print 'params (n,p,t,rho,eta)',(n,p,t,rho,eta)
    print 'number of samples p+t',p+t
   
    #random generation of a CRT-ACD instance
    prime_numbers=[random_prime(2^eta,False,2^(eta-1)) for i in range(n)]
    M=prod(prime_numbers)
    r=[[ZZ.random_element(-2^rho+1,2^rho) for i in range(n)] for j in range(p)]
    x=[modNear(crt(rj,prime_numbers),M) for rj in r]
    y=[modNear(crt([ZZ.random_element(-2^rho+1,2^rho) for i in range(n)],prime_numbers),M) for a in range(t)]
   
    time0=cputime()
    #define the vector of product CRT-ACD Samples
    z=x
    for a in range(t):
        z=z+[mod(xi*y[a],M).lift() for xi in x]
 
    #1st step: Orthogonal lattice attack using LLL
    dim=(t+1)*p
    Mat=matrix(ZZ,dim,dim)
    for i in range(dim -1):
        Mat[i,i]=1
        Mat[i,dim-1]=mod(-z[i]*inverse_mod(z[dim-1],M),M)
        Mat[dim-1,dim-1]=M
 
    MatReduced=Mat.LLL()
    V=MatReduced[:dim-n].right_kernel().matrix()
   
    #2nd step: Solve Problem C
    W0=matrix(GF(prime),V[:,:p].T)
    listW=[matrix(GF(prime),V[:,((a+1)*p):((a+2)*p)].T) for a in range(t)]
    S=SOLVE_C(W0,listW,n,p,prime)
    SmodNear=[[modNear(ZZ(s),prime) for s in S[a]] for a in range(t)]
    #eigenvalues (diagonal entries of diagonal entries)
    found=[sorted(SmodNear[a]) for a in range(t)]
    #recovered primes by computing gcds
    recovered_primes=Set([gcd(M,ZZ(y[0]-ZZ(ti))) for ti in found[0]])
   
    print 'Number of primes recovered:',len(Set(prime_numbers).intersection(recovered_primes))
    print 'out of',n
 
    print 'running time',cputime()-time0
 
#Application 2: cryptanalysis of CLT13 by improving the attack of Cheon et al.
 
#A preliminary function to generate random CLT13-encodings
def random_encoding(rho,prime_numbers):
    return crt([ZZ.random_element(2^rho) for i in range(len(prime_numbers))],prime_numbers)
 
#algorithm to improve the attack of Cheon et al.
#input: n (dimension of CLT13), p,t, rho (noise bit-size in encodings), eta (bit-size of prime factors), prime (a prime number to speed up by computing over F_prime)
def improve_cheon(n,p,t,eta,rho,prime):
    print 'params (n,p,t,rho,eta)',(n,p,t,rho,eta)
    print 'total number of encodings 2p+t',(2*p+t,2*n+2)
    prime_numbers=[random_prime(2^eta,False,2^(eta-1)) for i in range(n)]
    x0=prod(prime_numbers)
 
    #zero-test parameter
    pzt=crt([ZZ.random_element(2^rho)*x0/pi for pi in prime_numbers],prime_numbers)
   
    #Public sets of encodings
    SetA=[random_encoding(rho,prime_numbers) for i in range(p)]
    SetB=[random_encoding(rho,prime_numbers) for a in range(t)]
    SetC=[random_encoding(rho,prime_numbers) for i in range(p)]
 
    time0=cputime()
    #generate matrices by zero-testing
    listW=[]
    for a in range(t):
        listW.append(matrix(GF(prime),[[ai*cj*SetB[a]*pzt%x0 for cj in SetC] for ai in SetA]))
    #Solve Problem D
    S=SOLVE_D(listW[0],listW[1:t],n,p,prime)
    #S=SOLVE_D(V,listW,n,p,prime)
    
    #reveal prime factors of x0 by rational reconstruction and computing gcds
    S0ZZ=[rational_reconstruction(modNear(si,prime),prime) for si in S[0]]
    recovered_primes=[gcd(x0,(ratio.numerator()*SetB[0]-ratio.denominator()*SetB[1])) for ratio in S0ZZ]
   
    print'running time',cputime()-time0
 
    print 'Number of primes recovered:',len(Set(prime_numbers).intersection(Set(recovered_primes)))
    print 'out of',n

#Examples

#print test_Algorithm_C(25,8,7,next_prime(2^500))
#print test_Algorithm_D(25,18,4,next_prime(2^500))
#print improve_crtacd(30,8,7,700,100,next_prime(2^710))
#print improve_cheon(30,22,5,700,100,next_prime(2^710))