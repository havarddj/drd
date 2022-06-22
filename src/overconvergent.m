/* From "overconvergentlatest.m" */
/* (from Jan's email a 21/01/22 */

// -------------------------------------------------------------
//               2) Overconvergent modular forms
// -------------------------------------------------------------

// This section contains routines to compute explicitly with spaces of overconvergent modular forms.
// The algorithms are due to Lauder, though we have restricted here to level 1 where things are much simpler. 


// Computes the q-expansion for the Eisenstein series of weightk, to precision q^NN over S.
function ESeries(k,NN,S)

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

end function;


// Dimension of space of modular forms of weight k and level 1.
function DimensionClassicalSpace(k)

	if ((k mod 2) eq 1) or (k lt 0) then
		return 0;
	end if;
	kmod12 := k mod 12;
	if (kmod12 eq 2) then
		return Floor(k/12);
	else
		return Floor(k/12) + 1;
	end if;

end function;


// Returns the power of the Hasse invariant that has been lifted.
// This is always 1, except when p = 2,3.

function ap(p)

	a := 1;
	if p eq 2 then
		a := 4;
	end if;
	if p eq 3 then 
		a := 3;
	end if;
	return a;

end function;


// Returns the weight of the Eisenstein series to be used for lifting the Hasse invariant. 
// This is always p-1, unless p = 2,3.

function EisWeight(p)

	return ap(p)*(p-1);

end function;


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


// Returns list e of Katz expansions, 
function OverconvergentBasis(k,p,mp,prec,S)
	
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

end function;


// -------------------------------------------------------------
//                   3) Ordinary projections
// -------------------------------------------------------------

// This section computes the ordinary projection of an overconvergent form G, by iterating Up. 

// Given a form G in a space with basis B, recognise G as a linear combination of the elements in B.
/* function basis_coordinates(G,B : prt := false) */

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

/* end function; */


function basis_coordinates(G,B : prt := true)

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
	constant := -(&+ [Coefficient(B[i],0)*comb[i] : i in [1..#B]])/Rp!comb[#B+1];
	print "Constant term is: ", constant;
    end if;
	
    return constant, comb;

end function;


// Test whether a given form is overconvergent of weight 2 and tame level 1.
function IsOverconvergent(G : prt := false)

	prec := Precision(Parent(Coefficient(G,1)));
	p := Prime(Parent(Coefficient(G,1)));
	m := Precision(Parent(G));
	B := OverconvergentBasis(2,p,m,prec,Parent(Coefficient(G,1)));
	
	constant, comb := basis_coordinates(G,B : prt := prt);
	
	return constant;
	
end function;



// Computes the ordinary projection of G, in the space of overconvergent forms of weight 2 and tame level 1.
function OrdinaryProjection(G : prt := false) 

	Rp   := Parent(Coefficient(G,0));
	prec := Precision(Rp);
	p    := Prime(Rp);
	m    := Precision(Parent(G));
	bnd  := DimensionClassicalSpace(2+EisWeight(p)*Floor(prec*(p+1)/(ap(p)*p)))-1;
	
	if bnd ge m then
		print "You need at least", bnd, "Fourier coefficients to compute the ordinary projection.";
		return "","";
	else
	
		t0 := Cputime();
		B  := OverconvergentBasis(2,p,p*m,prec,Parent(Coefficient(G,1)));
		print "Computed overconvergent basis: ", Cputime() - t0;		
		
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
		/* Apow := 1;  */
		/* for i := 1 to m do */
		/* 	Apow := Apow*A2; */
		/* end for; */

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
		
	end if;

end function;


// -------------------------------------------------------------
//                 4) Spectral decompositions
// -------------------------------------------------------------

// Check that a given q-expansion is (modulo the constant term) a member of the space  M_2(p).
function IsClassical(G : prt := true)

	Kp := Parent(Coefficient(G,0));
	Rp := IntegerRing(Kp);
	p  := Prime(Rp);
	m  := Precision(Parent(G));
	M  := ModularForms(Gamma0(p),2);
	B  := Basis(EisensteinSubspace(M),m) cat Basis(CuspForms(Gamma0(p),2),m);
		
	constant, comb := basis_coordinates(G,B : prt := prt);
	
	if prt eq true then
		print "Basis: ", B;
	end if;
	vec := [Rp!(-Coefficient(B[1],1)*comb[1]/comb[#B+1])] cat [Rp!(-comb[i]/comb[#B+1]) : i in [2..#B]];
// 	assert &+vec eq Coefficient(G,1);
// 	print "Should be constant: ", &+[vec[i]*B[i]/Coefficient(B[i],1) : i in [1..#vec]] - G;
	
	return vec, B;

end function;


// Check that a given q-expansion is (modulo the constant term) a member of the space  M_2(p).
function IsClassicalForm(G,k,N)

	m  := Precision(Parent(G));
	M := ModularForms(Gamma0(N),k);
	B := Basis(EisensteinSubspace(M),m) cat Basis(CuspForms(Gamma0(N),k),m);
		
	constant, comb := basis_coordinates(G,B : prt := true);
	
	return [-Coefficient(B[1],1)*comb[1]/comb[#B+1]] cat [-comb[i]/comb[#B+1] : i in [2..#B]];

end function;
