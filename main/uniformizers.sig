177,0
S,InverseJFunction,Returns a tau such that j(tau) = j. The source is https://math.stackexchange.com/questions/438436/inverting-the-modular-j-function,0,1,0,0,0,0,0,0,0,172,,172,-38,-38,-38,-38,-38
S,TaylorExpansion,Computes the Taylor expansion of f(q) at q0,0,2,0,0,0,0,0,0,0,172,,0,0,285,,285,-38,-38,-38,-38,-38
S,Q,Returns Q(tau) = e^(2 pi i tau),0,1,0,0,0,0,0,0,0,172,,172,-38,-38,-38,-38,-38
S,GetUniformizer,"Returns a local uniformizer around the residue disk of the basepoint as a power series in q, NOT necessarily at the basepoint itself. The uniformizer is: (1) j(q)^(1/3) if j equiv 0 and g[1,1,-1,0]g^(-1) does not lie in Gamma_H. (2) (j(q)-1728)^(1/2) if j equiv 1728 and g[0,-1,1,0]g^(-1) does not lie in Gamma_H. (3) Hilbert class polynomial of j otherwise",0,1,0,0,0,0,0,0,0,Basepoint,,285,312,148,-38,-38,-38
S,ChangeUniformizer,Changes the uniformizer of f from q to that of the basepoint,0,2,0,0,0,0,0,0,0,Basepoint,,0,0,285,,82,-38,-38,-38,-38,-38
