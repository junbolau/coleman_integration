177,0
T,BasicBasepoint,Basepoint,0
A,BasicBasepoint,13,p,pp,v,c_v,tau,j_modp,ap,bp,D,K,H_O,j,discrim
A,Basepoint,6,B,H,N,g,gamma,tau_new
T,CuspBasepoint,-,0
A,CuspBasepoint,5,H,N,g,gamma,r
T,PlcNumEltWithConj,-,0
A,PlcNumEltWithConj,2,v,c_v
S,NewPlaceWithConj,Constructor,0,2,0,0,0,0,0,0,0,36,,0,0,332,,PlcNumEltWithConj,-38,-38,-38,-38,-38
S,Evaluate,Evaluates alph at the place v,0,2,0,0,0,0,0,0,0,PlcNumEltWithConj,,0,0,28,,172,-38,-38,-38,-38,-38
S,InfinitePlacesWithConj,"Given a number field, returns the infinite places with conjugation",0,1,0,0,0,0,0,0,0,27,,82,-38,-38,-38,-38,-38
S,MakeBasicBasepoint,Constructor,0,6,0,0,0,0,0,0,0,148,,0,0,148,,0,0,PlcNumEltWithConj,,0,0,217,,0,0,28,,0,0,28,,BasicBasepoint,-38,-38,-38,-38,-38
S,FrobeniusMatrix,Returns the Frobenius matrix of the base point,0,2,0,0,0,0,0,0,0,BasicBasepoint,,0,0,148,,178,-38,-38,-38,-38,-38
S,FindLevelStructures,"Finds the possible level structures on B defined over F_p NOTE: This code assumes that [0,-1,1,0], and [1,1,-1,0] are the automorphism matrices when a priori they might be only be conjugate to that matrix. This is fine because in GenerateBasicBasepoints we have hardcoded in the basepoints for j-invariants 0 and 1728. The downside is that you do not get anything about the Frobenius matrix if p is inert in one of those number fields",0,3,0,0,0,0,0,0,0,BasicBasepoint,,0,0,178,,0,0,148,,82,-38,-38,-38,-38,-38
S,FindCuspLevelStructures,Finds all cusp level structures defined over F_p,0,3,0,0,0,0,0,0,0,148,,0,0,178,,0,0,148,,82,-38,-38,-38,-38,-38
S,Print,Print BasicBasepoint,0,1,0,0,1,0,0,0,0,BasicBasepoint,,-38,-38,-38,-38,-38,-38
S,MakeBasepoint,Constructor for Basepoint,0,4,0,0,0,0,0,0,0,BasicBasepoint,,0,0,180,,0,0,178,,0,0,148,,Basepoint,-38,-38,-38,-38,-38
S,MakeCuspBasepoint,Constructor for CuspBasepoint,0,3,0,0,0,0,0,0,0,180,,0,0,178,,0,0,148,,CuspBasepoint,-38,-38,-38,-38,-38
S,Parent,Parent of BB,0,1,0,0,0,0,0,0,0,Basepoint,,BasicBasepoint,-38,-38,-38,-38,-38
S,Print,Print Basepoint,0,1,0,0,1,0,0,0,0,Basepoint,,-38,-38,-38,-38,-38,-38
S,Print,Print CuspBasepoint,0,1,0,0,1,0,0,0,0,CuspBasepoint,,-38,-38,-38,-38,-38,-38
S,GetRamification,Get ramification of the cusp,0,1,0,0,0,0,0,0,0,CuspBasepoint,,148,-38,-38,-38,-38,-38
S,GetWidth,Gets the width of the cusp g*iinfty,0,3,0,0,0,0,0,0,0,180,,0,0,148,,0,0,178,,148,-38,-38,-38,-38,-38
S,GetWidth,Gets the width of the infinite cusp,0,2,0,0,0,0,0,0,0,148,,0,0,178,,148,-38,-38,-38,-38,-38
S,GetRamification,Get ramification of the point,0,1,0,0,0,0,0,0,0,Basepoint,,148,-38,-38,-38,-38,-38
S,GenerateBasicBasepoints,Generates a list of non-cuspidal basepoints whose j-invariants cover all residue classes mod p,0,1,0,0,0,0,0,0,0,148,,82,-38,-38,-38,-38,-38
S,GenerateAllBasepoints,"Generates all possible noncuspidal basepoints, WITH the level structure",0,3,0,0,0,0,0,0,0,148,,0,0,178,,0,0,148,,82,-38,-38,-38,-38,-38
