// Given a prime p, a different prime l < 37, and j(E), computes the j-invariants of the quotients of E by each order l subgroup. 
a := function(p, l, j)
    assert l lt 37;
    I := Open("modpolys/phi_j_" cat IntegerToString(l) cat ".txt", "r");
    ReadObjectCheck(I);
end;
