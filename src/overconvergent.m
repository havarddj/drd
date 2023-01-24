/* From "overconvergentlatest.m" */
/* (from Jan's email a 21/01/22 */
/* Updated 14/10/22 to incorporate higher level katz */
/* Updated 05/12/22 to make use of intrinsics */

/* Most of the below was originally written by Jan Vonk: */
// -------------------------------------------------------------
//               2) Overconvergent modular forms
// -------------------------------------------------------------

// This section contains routines to compute explicitly with spaces of overconvergent modular forms.
// The algorithms are due to Lauder, though we have restricted here to level 1 where things are much simpler. 


import "./OClvlN.m" : Computeldash, HigherLevelKatzExp;

ZZ := Integers();
	      
intrinsic ESeries(k,NN,S) -> Any
{Computes the q-expansion for the Eisenstein series of weightk, to precision q^NN over S.}
	R<q> := PowerSeriesRing(S,NN);
	a1 := -S!(2*k/Bernoulli(k));
	Ek := 1 + a1*q;
	for n := 2 to NN-1 do
		coeffn := 0;
		divs := Divisors(n);
		for d in divs do
			coeffn := coeffn + d^(k-1);
		end for;
		Ek := Ek + a1*coeffn*q^n;
	end for;

	return Ek;

end intrinsic;


/* */
intrinsic DimensionClassicalSpace(k) -> Any
{ Dimension of space of modular forms of weight k and level 1}
	if ((k mod 2) eq 1) or (k lt 0) then
		return 0;
	end if;

	if (k mod 12) eq 2 then
		return Floor(k/12);
	else
		return Floor(k/12) + 1;
	end if;

end intrinsic;


//
// This is always 1, except when p = 2,3.

intrinsic ap(p) -> Any
{ Returns the power of the Hasse invariant that has been lifted.}
	a := 1;
	if p eq 2 then
		a := 4;
	end if;
	if p eq 3 then 
		a := 3;
	end if;
	return a;

end intrinsic;


// 
// This is always p-1, unless p = 2,3.

intrinsic EisWeight(p) -> Any
{Returns the weight of the Eisenstein series to be used for lifting the Hasse invariant. }
	return ap(p)*(p-1);

end intrinsic;


// Returns basis for a subspace of weight k complementary to image of multiplication by the Eisenstein series. 
function ComputeWi(k,p,delta,deltaj,E4,E6)
	
	// Define a and b
	a := k mod 3;
	b := (k div 2) mod 2;
		
	// Compute dimensions required for Miller basis
	d  := DimensionClassicalSpace(k) - 1;
	e  := DimensionClassicalSpace(k - EisWeight(p)) - 1;
	Wi := [];
	for j := e+1 to d do
		// compute aj = delta^j*E6^(2*(d-j) + b)*E4^a
		aj := deltaj*E6^(2*(d-j) + b)*E4^a;
		deltaj := deltaj*delta;
		Wi := Append(Wi,aj);
	end for;

	return Wi,deltaj;

end function;



intrinsic OverconvergentBasis(k,p,mp,prec,S) -> Any
{Returns list e of Katz expansions}
	
	Ep1 := ESeries(EisWeight(p),mp,S);
	E4  := ESeries(4,mp,S);
	E6  := ESeries(6,mp,S);
	q   := Parent(E4).1;
	del := Delta(q);
	
	delj := Parent(del)!1;
	B := [];	
	for i := 0 to Floor(prec*(p+1)/(ap(p)*p)) do
		Wi,delj := ComputeWi(k + i*EisWeight(p),p,del,delj,E4,E6);
		for bis in Wi do
			eis := p^(Floor(i*ap(p)*p/(p+1)))*Ep1^(-i)*bis;
// 			eis := Ep1^(-i)*bis;
			if eis ne 0 then
				B := Append(B,eis);
			end if;
		end for;
	end for;
		
	return B;

end intrinsic;


// -------------------------------------------------------------
//                   3) Ordinary projections
// -------------------------------------------------------------

// This section computes the ordinary projection of an overconvergent form G, by iterating Up. 

// Given a form G in a space with basis B, recognise G as a linear combination of the elements in B.
/* intrinsic basis_coordinates(G,B : prt := false) */

/* 	m := Precision(Parent(G)); */
/* 	C := Matrix([[Coefficient(B[i],j) : j in [1..m-1]] : i in [1..#B]] cat [[Coefficient(G,j) : j in [1..m-1]]]); */
/* 	K := Basis(Kernel(C)); */
/* 	if #K eq 0 then */
/* 		print "Not a combination of the basis elements!"; */
/* 		constant := 0; */
/* 	else */
/* 		comb := K[1]; */
/* 		constant := -(&+ [Coefficient(B[i],0)*comb[i] : i in [1..#B]])/comb[#B+1]; */
/* 		if prt eq true then */
/* 			print ""; */
/* 			print "Kernel is: "; */
/* 			print K; */
/* 			print ""; */
/* 			for i := 1 to #B do */
/* 				print "Valuation coordinate i: ", Valuation(comb[i]); */
/* 			end for; */
/* 			print "Constant term is: ", constant; */
/* 		end if; */
/* 	end if; */
	
/* 	return constant, comb; */

/* end intrinsic; */


intrinsic basis_coordinates(G,B : prt := true, int:=true) -> Any
{Finds G in terms of q-expansion basis B
This ignores the constant term, so if G misses a constant term it will be found and returned by the function.}
    Rp := Parent(Coefficient(G,1));
    m := Precision(Parent(G));
    C := Matrix([[Coefficient(B[i],j) : j in [1..m-1]] : i in [1..#B]] cat [[Coefficient(G,j) : j in [1..m-1]]]);
    K := Basis(Kernel(C));
    if #K eq 0 then
	print "Not a combination of the basis elements!";
	comb := 0;
	constant := 0;
    else
	/* Pick the right combination, based on the requirement that the final coefficient of the combination, corresponding to G, should have valuation 0 */
	/* j := 1;			 */
	/* while Valuation(K[j][#B+1]) gt 0 do */
	/*     j := j+ 1; */
	/* end while; */
	comb := K[1];
	/*  */
	if prt eq true then
	    print "";
	    print "Kernel is: ";
	    print K; /* K[1],K[2]/\* ,K[3]; *\/ */
		
	    print "";
	    for i := 1 to #B+1 do
		print "Valuation coordinate i: ", i, Valuation(comb[i]);
	    end for;
	    print "";
	    print "Coeff of G:", comb[#B+1];
	end if;
	if int then
	    try 
		constant := -(&+ [Coefficient(B[i],0)*comb[i] : i in [1..#B]])/Rp!comb[#B+1];
	    catch e1
		print "did not succeed writing in terms of basis, try with more precision";
		constant := 0;
	    end try;
	else
	    constant := -(&+ [Coefficient(B[i],0)*comb[i] : i in [1..#B]])/comb[#B+1];
	end if;
	print "Constant term is: ", constant;
    end if;
	
    return constant, comb;

end intrinsic;


// Test whether a given form is overconvergent of weight 2 and tame level f.
intrinsic IsOverconvergent(G : prt := false, f := 1) -> Any
{Test whether a given form is overconvergent of weight 2 and tame level f, and if so, return constant term}
    prec := Precision(Parent(Coefficient(G,1)));
    p := Prime(Parent(Coefficient(G,1)));
    m := Precision(Parent(G));

    if f eq 1 then
	B := OverconvergentBasis(2,p,m*p,prec,Parent(Coefficient(G,1)));
    else
	/* Does not work! */
	if prt then
	    print "computing basis of higher level Katz expansions";
	/* taken from the intrinsic HigherLevelUpGj in OClvlN.m */
	end if;
	elldash := Computeldash(p,f,2,m);
	elldashp := elldash*p;
	n := Floor(((p+1)/EisWeight(p))*(m+1+(ap(p)-1)/(p+1)));	 
	mdash := m + Ceiling(n*ap(p)/(p+1));
	weightbound := 6;	/* should be ok? */
	// Steps 2 and 3

	e, Ep1 := HigherLevelKatzExp(f,p,2,m,mdash,n,elldash,elldashp,weightbound);
	if prt then print "computed basis of Katz expansions"; end if;
	/* e is a matrix of coefficients, but we actually want a basis proper */
	R := Parent(G);
	q := R.1;
	B := [];

	for r in Rows(e) do
	    Append(~B,&+[ZZ!(r[i])*q^(i-1) : i in [1..Ncols(e)]]);
	end for;
	
    end if;
    if prt then
	print "Searching for form in space of overconvergent modular forms";
    end if;
    constant, comb := basis_coordinates(G,B : prt := prt);
    print "valuation of difference of terms";
    diffr := G - &+[comb[i]*B[i] : i in [1..#B]]/comb[#B+1];
    for i in [1..#B] do
	Valuation(Coefficient(diffr,i));
    end for;

    return constant;
	
end intrinsic;


intrinsic OrdinaryProjection(G : prt := false, f := 1) -> Any
{Computes the ordinary projection of G, in the space of overconvergent forms of weight 2 and tame level f}
    Rp   := Parent(Coefficient(G,0));
    prec := Precision(Rp);
    p    := Prime(Rp);
    m    := Precision(Parent(G))-1;
    bnd  := DimensionClassicalSpace(2+EisWeight(p)*Floor(prec*(p+1)/(ap(p)*p)))-1;
    if bnd gt m then
	print "You need at least", bnd, "Fourier coefficients to compute the ordinary projection.";
	print "number of coeffs", m;
	return "";
    end if;

    if f eq 1 then
	t0 := Cputime();
	B  := OverconvergentBasis(2,p,p*m,prec,Parent(Coefficient(G,1)));
	print "Computed overconvergent basis: ", Cputime() - t0;

    else
	elldash:=Computeldash(p,f,2,m);
	elldashp:=elldash*p;
	n:=Floor(((p+1)/EisWeight(p))*(m+1+(ap(p)-1)/(p+1)));	 
	mdash:=m + Ceiling(n*ap(p)/(p+1));
	weightbound := 6;	/* should be ok? */
	// Steps 2 and 3

	e,Ep1 :=HigherLevelKatzExp(f,p,2,m,mdash,n,elldash,elldashp,weightbound);
	/* e is a matrix of coefficients, but we actually want a basis proper */
	R<q> := PowerSeriesRing(Rp,Ncols(e));
	B := [];
	/* print "e has parent", Parent(e); */
	for r in Rows(e) do
	    Append(~B,&+[ZZ!(r[i])*q^(i-1) : i in [1..Ncols(e)]]);
	end for;
	/* print "Now B has parent", Parent(B); */
    end if;
		// Compute coefficients of image of basis under Up.
    ell := #B;
    S := Parent(Coefficient(B[1],0));
    T := ZeroMatrix(S,ell,ell);
    for i := 1 to ell do
	for j := 1 to ell do
	    T[i,j] := Coefficient(B[i],p*(j-1));
	end for;
    end for;
    
    // Solve for matrix for Up	
    t0 := Cputime();	
    A := ZeroMatrix(S,ell+1,ell+1);
    for i := 1 to ell do
	Ti := T[i];		
	for j := 1 to ell do
	    Bj := Parent(Ti)![Coefficient(B[j],l-1): l in [1 .. ell]];
	    lj := Integers()!Bj[j];
	    if lj eq 0 then
		print j, Bj;
	    end if;
	    A[i,j] := S!((Integers()!Ti[j])/lj);
	    Ti := Ti - A[i,j]*Bj;
	end for;
    end for;
    print "Computed matrix for Up:        ", Cputime() - t0;

    // Projection matrix
    t0 := Cputime();
    Apow := A^(2*m);
    /* A2 := A*A; */
    /* Bpow := 1; */
    /* for i := 1 to m do */
    /* 	Bpow := Bpow*A2; */
    /* end for; */

    /* assert Apow eq Bpow; */
    print "Computed projection matrix:    ", Cputime() - t0;

    // Projection of G.		
    constant, comb := basis_coordinates(G,B : prt := prt);
    comb_ord := comb*Apow;
    Gord := Parent(G)!0;
    print "den: ", comb[ell+1];
    den  := ZZ!(comb[ell+1]);
    /* den  := (comb[ell+1]); */
    for i := 1 to ell do
	Gord := Gord - Rp!(comb_ord[i]/den)*B[i];
	/* Gord := Gord - (comb_ord[i]/den)*B[i]; */
    end for;
    
    return Parent(G)!Gord;	
end intrinsic;


// -------------------------------------------------------------
//                 4) Spectral decompositions
// -------------------------------------------------------------


intrinsic IsClassical(G : prt := true, f := 1) -> Any
{Check that a given q-expansion is (modulo the constant term) a member of the space  M_2(pf).}
	Kp := Parent(Coefficient(G,0));
	Rp := IntegerRing(Kp);
	p  := Prime(Rp);
	m  := Precision(Parent(G));
	M  := ModularForms(Gamma0(p*f),2);
	B  := Basis(EisensteinSubspace(M),m) cat Basis(CuspForms(Gamma0(p*f),2),m);
		
	constant, comb := basis_coordinates(G,B : prt := prt);


	/* now normalise by the constant term of the Eisenstein
	series, at least when the level is p;    */
	/* if G = -\sum_i B[i]comb[i]/comb[#B+1], then replacing B[i]
	with B2[i] = B[i]/Coeff(B[i],1) gives G = -\sum_i
	B2[i]*Coeff(B[i])comb[i]/comb[#B+1]/  */
	/* so the new vec should be multiplied by Coeff[Bi] termwise*/

	vec := [];
	Bnorm := [];
	j := Dimension(EisensteinSubspace(M));
	for i in [1..j] do
	    Append(~vec, Rp!(-comb[i]*Coefficient(B[i],1)/comb[#B+1]));
	    Append(~Bnorm, B[i]/Coefficient(B[i],1));
	end for;
	for i in [j+1..#B] do
	    Append(~vec, Rp!(-comb[i]/comb[#B+1]));
	    Append(~Bnorm, B[i]);
	end for;
	assert &+vec eq Coefficient(G,1);
	if prt then
	    print "Should be constant: ", &+[Rp!vec[i]*Parent(G)!Bnorm[i] : i in [1..#vec]] - G;
	    print "normalised basis for M_2(Gamma0(pf)) given by", Bnorm;
	end if;
	return vec, Bnorm;

end intrinsic;



intrinsic IsClassicalForm(G,k,N) -> Any
{Check that a given q-expansion is (modulo the constant term) a member of the space  M_k(N)}
	m  := Precision(Parent(G));
	M := ModularForms(Gamma0(N),k);
	B := Basis(EisensteinSubspace(M),m) cat Basis(CuspForms(Gamma0(N),k),m);
		
	constant, comb := basis_coordinates(G,B : prt := true);
	
	return [-Coefficient(B[1],1)*comb[1]/comb[#B+1]] cat [-comb[i]/comb[#B+1] : i in [2..#B]];

end intrinsic;
