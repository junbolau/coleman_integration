import "./ModFrmGL2/ModSym/operators.m":
	HeckeGeneralCaseRepresentatives;

intrinsic HeckeDoubleCosetReps(N::RngIntElt, ell::RngIntElt, gens::SeqEnum) -> SeqEnum
{
	INPUTS: 
	* "N" -- integer, level
	* "ell" -- integer, coprime to N, Hecke operator T_ell
	* "gens" -- list, generators of G 

	OUTPUTS: 
	a matrix beta and a list of matrices alpha_i so that the double coset representatives for T_ell are given by 
	beta[1,0,0,ell]alpha_i
}

	G_ := sub<GL(2,Integers(N))|gens>;
	G := PSL2Subgroup(G_);
	beta := FindLiftToM2Z(Matrix(G`DetRep(ell))*Matrix(Integers(N),2,2,[1,0,0,1/ell]));
	alpha := beta * Matrix(Integers(),2,2,[1,0,0,ell]);
	GL2 := GL(2, Rationals());
	G_alpha_conj := Conjugate(G, GL2!alpha : IsExactLevel := true);
	G3 := G_alpha_conj meet G;
	cosets := Transversal(G, G3); 

	return [*Eltseq(beta), [Eltseq(mat): mat in cosets]*];
end intrinsic;

intrinsic HeckeAction(N::RngIntElt, ell::RngIntElt, gens::SeqEnum, coset_reps::List, prec::RngIntElt) -> ModMatRngElt
{
	INPUTS:
	* "N" -- integer, level
	* "ell" -- integer, coprime to N, Hecke operator T_ell
	* "gens" -- list, generators of G 
	* "prec" -- integer, precision
	* "beta" -- list
	* "alpha_list" -- list

	OUTPUT: 
	matrix representing the action of the Hecke operator T_ell on a certain basis of cusp forms given by q-expansions 
}
	K<zeta_N> := CyclotomicField(N);
	M<zeta_Nell>:= CyclotomicField(N*ell);
	Embed(K,M,zeta_Nell^ell);
	a,b,c,d := SL2ActionOnCuspForms(N,2,prec: HNF:=true);
	G := sub<GL(2,Integers(N))|gens>;
	basislist:= ComputeModularFormsForXG(G,2,prec);
	len := #basislist;
	B := ChangeRing(b,K);

	basislist_coeff := [[0 : j in [1..prec]]: i in [1..len]];
	for i in [1..len] do
		for j in [1..prec] do
			basislist_coeff[i][j] := Coefficient(basislist[i], j);
		end for;
	end for;


	sol_list := [Transpose(Solution(B,Matrix(K,1,prec,basislist_coeff[i]))) : i in [1..len]];

	beta := coset_reps[1];
	alpha_list := coset_reps[2];

	// action of beta  
	beta_matrix := Transpose(d(Matrix(2,2,beta)));

	q_exp_beta_action_basis := [Transpose(beta_matrix*sol_j)*B : sol_j in sol_list];

	// slash k-operator with [1,0,0,p]
	v_ell_list := [Matrix(1,prec,[1/ell*bqexp[1][n] : n in [1 .. prec]]) : bqexp in q_exp_beta_action_basis];

	a2,b2,c2,d2 := SL2ActionOnCuspForms(N*ell,2,prec: HNF:=true);
	B2 := ChangeRing(b2, M);
	sol_list2 := [Transpose(Matrix(M,1,Nrows(B2),[Solution(B2,ChangeRing(v_ell_list[i][1], M))])) : i in [1..len]];

	// action by alpha_i's
	alpha_matrices:= [Transpose(d2(Matrix(2,2,i))) : i in alpha_list];
	q_exp_alpha_action_basis := [[Transpose(alpha_i*sol_j)*B2 : alpha_i in alpha_matrices] : sol_j in sol_list2];

	bound := Floor(prec/ell);

	action_list := [&+q_exp_alpha_action_basis[i] : i in [1..len]];
	image_matrix := Matrix(len, bound, [[action_list[i][1][j*ell] : j in [1 .. bound]] : i in [1 .. len]]);
	basis_matrix := Matrix(len, bound, [basislist_coeff[i][1 .. bound] : i in [1 .. len]]);
	hecke_matrix := Solution(basis_matrix, ChangeRing(image_matrix, BaseRing(basis_matrix))); // hecke_matrix*basis_matrix = image_matrix

	return hecke_matrix;
end intrinsic; 
