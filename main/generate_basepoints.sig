177,0
S,CompatiblePrimes,"Given a number field K, a prime pp of K above p, and a number field L, return a list of primes ppp of L above p ""compatible"" with pp. The fields K and L are assumed to be Galois over Q",0,4,0,0,0,0,0,0,0,148,,0,0,217,,0,0,27,,0,0,27,,82,-38,-38,-38,-38,-38
T,BasicBasepoint,Basepoint,0
T,CuspBasepoint,-,0
A,BasicBasepoint,11,p,pp,v,c_v,tau,j_modp,ap,bp,D,K,H_O
A,Basepoint,4,H,N,g,B
A,CuspBasepoint,4,H,N,g,r
S,MakeBasicBasepoint,Constructor,0,6,0,0,0,0,0,0,0,148,,0,0,36,,0,0,332,,0,0,217,,0,0,28,,0,0,85,,BasicBasepoint,-38,-38,-38,-38,-38
S,FrobeniusMatrix,Returns the Frobenius matrix of the base point,0,2,0,0,0,0,0,0,0,BasicBasepoint,,0,0,148,,178,-38,-38,-38,-38,-38
S,Q,Returns Q(tau) = e^(2 pi i tau),0,1,0,0,0,0,0,0,0,-1,,172,-38,-38,-38,-38,-38
S,FindLevelStructures,"Finds the possible level structures on B defined over F_p NOTE: This code assumes that [0,-1,1,0], and [1,1,-1,0] are the automorphism matrices when a priori they might be only be conjugate to that matrix. This is fine because in GenerateBasicBasepoints we have hardcoded in the basepoints for j-invariants 0 and 1728. The downside is that you do not get anything about the Frobenius matrix if p is inert in one of those number fields",0,3,0,0,0,0,0,0,0,BasicBasepoint,,0,0,178,,0,0,148,,82,-38,-38,-38,-38,-38
S,FindCuspLevelStructures,Finds all cusp level structures defined over F_p,0,3,0,0,0,0,0,0,0,148,,0,0,178,,0,0,148,,82,-38,-38,-38,-38,-38
S,Print,Print BasicBasepoint,0,1,0,0,1,0,0,0,0,BasicBasepoint,,-38,-38,-38,-38,-38,-38
S,MakeBasepoint,Constructor for Basepoint,0,4,0,0,0,0,0,0,0,BasicBasepoint,,0,0,180,,0,0,178,,0,0,148,,Basepoint,-38,-38,-38,-38,-38
S,MakeCuspBasepoint,Constructor for CuspBasepoint,0,3,0,0,0,0,0,0,0,180,,0,0,178,,0,0,148,,CuspBasepoint,-38,-38,-38,-38,-38
S,Parent,Parent of BB,0,1,0,0,0,0,0,0,0,Basepoint,,BasicBasepoint,-38,-38,-38,-38,-38
S,Print,Print Basepoint,0,1,0,0,1,0,0,0,0,Basepoint,,-38,-38,-38,-38,-38,-38
S,Print,Print CuspBasepoint,0,1,0,0,1,0,0,0,0,CuspBasepoint,,-38,-38,-38,-38,-38,-38
S,GenerateBasicBasepoints,Generates a list of non-cuspidal basepoints whose j-invariants cover all residue classes mod p,0,1,0,0,0,0,0,0,0,148,,82,-38,-38,-38,-38,-38
S,GenerateAllBasepoints,"Generates all possible noncuspidal basepoints, WITH the level structure",0,3,0,0,0,0,0,0,0,148,,0,0,178,,0,0,148,,82,-38,-38,-38,-38,-38
