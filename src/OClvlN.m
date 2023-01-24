/*

January 3, 2012

Copyright (C) 2012 Alan Lauder                                            
 
Written by Alan Lauder.

***

Instructions:

HeckeSeries(p,N,k,m: weightbound) : ->

The characteristic series P(t) modulo p^m of the Atkin U_p operator
acting upon the space of overconvergent p-adic modular forms of level
Gamma_0(N) and weight k. Here p >= 5 is a prime not dividing N, k an
integer and m a positive integer.  The optional parameter weightbound
gives an (even integer) bound on the weight of the generators which
are chosen for certain spaces of classical modular forms required at
one point in the algorithm for level N>=2. This takes the default
value weightbound := 6; however, for some levels the algorithm will
terminate more quickly if one sets weightbound := 4. (One may have to
choose a higher value for weightbound though if one finds the
algorithm fails to terminate for some small levels.)

The input k may also be taken to be a sequence kseq of weights all
congruent modulo (p-1). In this case the output is the corresponding
sequence of characteristic series'. (This is faster than computing for
each weight separately.)

Provided m<=k-1 then P(t) is the reverse characteristic polynomial
modulo p^m of the Atkin U_p operator on the space of classical modular
forms of level Gamma_0(Np) and weight k, by Coleman's theorem. In
addition, provided m <= (k-2)/2 then P(t) is the reverse
characteristic polynomial modulo p^m of the Hecke T_p operator on the
space of classical modular forms of level Gamma_0(N) and weight k.

The algorithm gives a provably correct output but for level N>=2 uses
randomisation and may not terminate in certain exceptional cases.

The algorithm used is "Algorithms 1 and 2" in "Computations with
classical and p-adic modular forms" by Alan Lauder, in LMS
J. Comput. Math. 14 (2011), 214-231 (and Newton's formula for finding
the coefficients of the characteristic polynomial of a matrix). We use
suggestions of David Loeffler and John Voight to generate certain
spaces of classical modular forms for level N>=2.  The algorithm has a
running time which is linear in log(k), and the implementation is
especially fast for level N := 1.

HeckeSeriesDegreeBound(p,N,k,m) : ->

Gives a bound on the degree of the characteristic series P(t) modulo
p^m of the Atkin U_p operator on the space of overconvergent p-adic
modular forms of (even) weight k and level Gamma_0(N).  This bound is
due to Daqing Wan and depends only upon k modulo (p-1) rather than k
itself.

***

Examples:

> time P:=HeckeSeries(5,41,2,5); 
Time: 11.460
> P;
625*t^22 + 1500*t^21 + 1300*t^20 + 1300*t^19 - 86*t^18 - 1093*t^17 - 1336*t^16 + 1231*t^15 - 
    565*t^14 + 911*t^13 - 662*t^12 + 591*t^11 + 764*t^10 + 505*t^9 + 991*t^8 - 352*t^7 + 576*t^6
    + 154*t^5 + 985*t^4 + 1234*t^3 + 532*t^2 + 269*t + 1
> time Pseq:=HeckeSeries(7,3,[1000,1006],5);               
Time: 0.140
> Pseq;
[
    7203*$.1^6 - 4116*$.1^5 + 6713*$.1^4 - 700*$.1^3 - 4675*$.1^2 - 4426*$.1 + 1,
    2401*$.1^6 + 8134*$.1^4 - 3976*$.1^3 + 5160*$.1^2 + 5087*$.1 + 1
]
> time Pseq:=HeckeSeries(7,3,[1000,1006],5: weightbound := 4);
Time: 0.110
> HeckeSeriesDegreeBound(7,3,1000,5);
9
> time P:=HeckeSeries(29,1,10000,10);                                                                  
Time: 1.450
> P;
134393786323419*t^8 - 174295724342741*t^7 - 174857545225000*t^6 - 153412311426730*t^5 + 
    41820892464727*t^4 - 148803482429283*t^3 - 111232323996568*t^2 + 165679475331974*t + 1


***

This is free software: it is made available in the hope that it will be useful, but without any warranty.

*/

//  *** AUXILIARY CODE FOR GENERAL LEVEL ***

// CLASSICAL MODULAR FORMS

// Returns Eisenstein series E_k over given ring S modulo q^NN normalised
// to have constant term a_0 = 1.

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

// DEGREE BOUND AND CHARACTERISTIC SERIES

// Returns dimension of space of classical modular forms for Gamma_0(N) of weight k.	

function DimensionMNk(N,k)

	if k gt 0 then
		return Dimension(ModularForms(N,k));
	elif k eq 0 then
		return 1;
	else // k < 0
		return 0;
	end if;

end function;

// Writing A := UpGj(p,N,k,m), the function returns d with deg(det(1 - At)) <= d.
// Uses Lemma 3.1. in D. Wan "Dimension variation of classical
// and p-adic modular forms", Invent. Math. 133, (1998) 449-463.

function HeckeSeriesDegreeBound(p,N,k,m)

	k0:=k mod (p-1);
	ds:=[DimensionMNk(N,k0)];
	ms:=[ds[1]];
	sum:=0;
	u:=1;
		
	repeat
		Append(~ds,DimensionMNk(N,k0 + u*(p-1)));
		Append(~ms,ds[u+1] - ds[u]);
		sum:=sum + u*ms[u+1];
		ord:=Floor(((p-1)/(p+1))*sum - ds[u+1]);
		u:=u+1;
	until ord ge m;	

	return (ds[u]-1);	

end function;

// Given square matrix A over Z/(p^m) returns det(1 - A t)
// Note: matrix should be over IntegerRing(p^m) rather
// than pAdicRing(p^m) for otherwise it takes forever.

function ReverseCharacteristicPolynomial(A)
	
	P:=CharacteristicPolynomial(A);
	return ReciprocalPolynomial(P);
	
end function;

// Check kseq contains weights congruent modulo p-1.

function IsValidWeightSequence(kseq,p)

	len:=#kseq;
	if len eq 0 then
		return false;
	end if;
	
	result:=true;
	k0:=kseq[1] mod (p-1);
	for i:=2 to len do
		if (kseq[i] mod (p-1)) ne k0 then
			result:=false;
		end if;
	end for;

	return result;

end function;

// *** LEVEL N > 1 ***

// CLASSICAL MODULAR FORMS AND LINEAR ALGEBRA

// Converts a "modular form" to power series in q over Zp/(p^mdash).

function qexpToPS(f,p,mdash,NN)

	M:=Parent(f);
	Zp:=IntegerRing(p^mdash);
	R<q>:=PowerSeriesRing(Zp,NN);
	
	fPS:=R!0;
	for i:=0 to NN-1 do
		fPS:=fPS + Coefficient(f,i)*q^i;
	end for;
	
	return fPS;

end function;

// Constructs bases of power series expansions for modular forms of level
// Gamma_0(N) and (even) weight k <= weightbound.
// The basis elements are in Zp[[q]]/(p^m,q^NN).

function LowWeightBases(N,p,mdash,NN,weightbound)

	generators:=[];

	for k:=2 to weightbound by 2 do
		M:=ModularForms(N,k); // Gamma_0(N)
		b:=Basis(M,NN);
		basisweightk:=[];
		for f in b do
			Append(~basisweightk,qexpToPS(f,p,mdash,NN));
		end for;
		Append(~generators,basisweightk);
	end for;

	return generators;

end function;

// Returns "random" bases for spaces of modular forms of level Gamma_0(N) and
// (even) weight k <= weightbound. The basis elements are in Zp[[q]]/(p^mdash,q^NN).
// The random bases are chosen to be ones for modular forms with coefficients in Zp.

function RandomLowWeightBases(N,p,mdash,NN,weightbound)

	LWB:=LowWeightBases(N,p,mdash,NN,weightbound);
	R:=Parent(LWB[1][1]);
	
	RandomLWB:=[];

	for i:=1 to #LWB do // weight k = 2*i
		basisweightk:=LWB[i];
		dimweightk:=#basisweightk;
		coeffsmat:=Random(GL(dimweightk,p));
		randombasisweightk:=[];
		for j:=1 to dimweightk do
			coeffsmatj:=coeffsmat[j];
			f:=R!0;
			for l:=1 to dimweightk do
				f:=f + (Integers()!coeffsmatj[l])*basisweightk[l];
			end for;
			Append(~randombasisweightk,f);
		end for;
		Append(~RandomLWB,randombasisweightk);
	end for;

	return RandomLWB;

end function;


// Computes "random" solution in non-negative integers to
// equation a_1 + 2 a_2 + 3 a_3 + ... + B a_B = K.
// It uses a greedy algorithm and the output is not uniformly
// distributed.

function RandomSolution(B,K)

	a:=[];
	for i:=B to 2 by -1 do
		ai:=Random(0,Floor(K/i));
		Append(~a,ai);
		K:=K - ai*i;
	end for;
	a1:=K;
	Append(~a,a1);
	arev:=Reverse(a);
	
	return arev;
	
end function;


// Returns position of the leading entry of a vector.

function LeadingPosition(v)

	d:=Dimension(Parent(v));	
	i:=1;
	vi:=v[i];
	while vi eq 0 do
		i:=i+1;
		vi:=v[i];
	end while;
	
	return i;

end function;

// Returns leading entry of a vector.

function LeadingEntry(v)

	return v[LeadingPosition(v)];

end function;

// Given as input a list of elements in Z[[q]]/(p^mdash,q^NN) it returns
// the "row-reduced form" of this list and its length (rank).

function RowReducedForm(basis)

	dim:=#basis;
	R<q>:=Parent(basis[1]);
	NN:=Precision(R);
	Zpm:=BaseRing(R);
	M:=ZeroMatrix(Zpm,dim,NN);
	
	// extract coeffs as matrix
	for i:=1 to dim do
		for j:=1 to NN do
			M[i,j]:=Coefficient(basis[i],j-1);
		end for;
	end for;

	// reduce
	Mred:=EchelonForm(M);
	rk:=Rank(Mred);
	
	// recover as series
	basisred:=[];
	for i:=1 to rk do
		basisredi:=R!0;
		for j:=1 to NN do
			basisredi:=basisredi + Mred[i,j]*q^(j-1);
		end for;
		Append(~basisred,basisredi);
	end for;
	
	return basisred,rk;

end function;

// COMPLEMENTARY SPACES.

// Auxiliary function used in main loop of ComplementarySpacesModp

function RandomNewBasisModp(N,p,k,LWBModp,OldBasisModp,weightbound)
	
	R:=Parent(LWBModp[1][1]); // power series ring mod p,q^elldash.
	
	// Case k0 + i(p-1) = 0 + 0(p-1) = 0
	if k eq 0 then 
		return [R!1],[[]]; // empty string <-> 1 for NewBasis.
	end if;
	
	// Case k = k0 + i(p-1) > 0
	di:=DimensionMNk(N,k);
	diminus1:=DimensionMNk(N,k-(p-1));
	mi:=di - diminus1;
	
	// Construct TotalBasisModp
	TotalBasisModp:=OldBasisModp; // Recall E_(p-1) = 1 mod p.
	
	// Generate mi new forms in weight k.
	NewBasisCode:=[];
	rk:=diminus1;
	for i:=1 to mi do // extra forms 
		while (rk lt diminus1 + i) do
			// construct random form of weight k
			exps:=RandomSolution(Floor(weightbound/2),k/2);
			TotalBasisi:=R!1;
			TotalBasisiCode:=[]; // empty string <-> 1.
			for j:=1 to #exps do // length exps is bound/2
				for l:=1 to (Integers()!exps[j]) do // pick exps[j] elements in weight 2*j
					a:=Random(1,#LWBModp[j]); // choose an index 
					TotalBasisi:=TotalBasisi*LWBModp[j][a]; // multiply by form
					Append(~TotalBasisiCode,[j,a]);
				end for;
			end for;
			Append(~TotalBasisModp,TotalBasisi);
			// Row-reduce new basis and compute rank.
			TotalBasisModp,rk:=RowReducedForm(TotalBasisModp);
		end while;
		Append(~NewBasisCode,TotalBasisiCode); // this one increased dimension.
	end for;
		
	return TotalBasisModp,NewBasisCode;

end function;

// Finds complementary spaces modulo p and returns a list of "codes" describing
// what products of basis forms were chosen.

function ComplementarySpacesModp(N,p,k0,n,elldash,LWBModp,weightbound)

	CompSpacesCode:=[];
	OldBasisModp:=[];
	for i:=0 to n do
		TotalBasisModp,NewBasisCodemi:=RandomNewBasisModp(N,p,k0 + i*(p-1),LWBModp,OldBasisModp,weightbound);
		Append(~CompSpacesCode,NewBasisCodemi);
		OldBasisModp:=TotalBasisModp; // basis for M_(k0 + i(p-1))
	end for;

	return CompSpacesCode;

end function;

// Reduces the basis of low weight forms mod (p,q^elldash).

function LowWeightBasesModp(LWB,p,elldash)

	R:=PowerSeriesRing(GF(p),elldash);
	LWBModp:=[];	
	
	for i:=1 to #LWB do // weight k = 2*i
		LWBModpWeightk:=[];
		for j:=1 to #LWB[i] do
			Append(~LWBModpWeightk,R!LWB[i][j]);
		end for;
		Append(~LWBModp,LWBModpWeightk);
	end for;
	
	return LWBModp;

end function;

// Returns complementary spaces W = [W_0,W_1,...,W_n] as list of 
// basis elements W_i modulo (p^mdash,q^elldashp).

function ComplementarySpaces(N,p,k0,n,mdash,elldash,elldashp,weightbound)

	// Find q-expansions for k <= weightbound mod (p^mdash,q^elldashp)

	LWB:=RandomLowWeightBases(N,p,mdash,elldashp,weightbound);
	
	// Find required products mod (p,q^elldash): this was suggested to the
	// author by John Voight.

	LWBModp:=LowWeightBasesModp(LWB,p,elldash);
	CompSpacesCode:=ComplementarySpacesModp(N,p,k0,n,elldash,LWBModp,weightbound);
		
	// Reconstruct products mod (p^mdash,q^elldashp)
	
	W:=[];
	
	Epm1:=ESeries(p-1,elldashp,IntegerRing(p^mdash));

	OldBasis:=[];
	for i:=0 to n do
		CompSpacesCodemi:=CompSpacesCode[i+1];
		Wi:=[];
		for k:=1 to #CompSpacesCodemi do
			// "code" <-> [ ... (k/2,a) ...] where k = weight, a = index of element
			// of weight k chosen, and then one takes the product over the list.
			CompSpacesCodemik:=CompSpacesCodemi[k];			
			Wik:=Parent(Epm1)!1;
			for j:=1 to #CompSpacesCodemik do 
				kby2:=CompSpacesCodemik[j][1];
				index:=CompSpacesCodemik[j][2];
				Wik:=Wik*LWB[kby2,index];
			end for;
			Append(~Wi,Wik);
		end for;
		Append(~W,Wi); 
	end for;

	return W;

end function;


// AUXILIARY CODE: KATZ EXPANSIONS

// Returns basis of Katz Expansions modulo (p^mdash,q^elldashp) as a matrix
// of coefficients. These are (part of) a basis for the space of overconvergent
// modular forms of level N and weight k0.

function HigherLevelKatzExp(N,p,k0,m,mdash,n,elldash,elldashp,weightbound)

	ordr:=1/(p+1); 
	S:=IntegerRing(p^mdash);
	Ep1:=ESeries(p-1,elldashp,S);
	R:=Parent(Ep1);
	q:=R.1;

	// construct basis as list of series

	W:=ComplementarySpaces(N,p,k0,n,mdash,elldash,elldashp,weightbound);
	KatzBasis:=[];
	for j:=0 to n do
		Wj:=W[j+1];
		dimj:=#Wj;
		Ep1minusj:=Ep1^-j;
		for i:=1 to dimj do
			wji:=Wj[i];
			b:=p^Floor(ordr*j)*wji*Ep1minusj;
			Append(~KatzBasis,b);
		end for;
	end for;
	
	// extract basis as matrix
	
	ell:=#KatzBasis;
	M:=ZeroMatrix(S,ell,elldashp);
	for i:=1 to ell do
		for j:=1 to elldashp do
			M[i,j]:=Coefficient(KatzBasis[i],j-1);
		end for;
	end for;
	
	// reduce: already in "almost" echelon form
	
	Mred:=EchelonForm(M);

	return Mred,Ep1; 

end function;

// Returns ldash, the Sturm bound.

function Computeldash(p,N,k0,m)

	n:=Floor(((p+1)/(p-1))*(m+1));
	ldash:=PrecisionBound(ModularForms(Gamma0(N),k0 + n*(p-1)));

	return ldash;

end function;


// MAIN FUNCTION.

// Returns matrix A modulo p^m in Step 5 of Algorithm 2 for each k in kseq.
// kseq has already been checked to have all weights congruent modulo (p-1).

function HigherLevelUpGj(p,N,kseq,m,weightbound)// Compute weight bound

	// Step 1
	
	k0:=kseq[1] mod (p-1);
	elldash:=Computeldash(p,N,k0,m);
	elldashp:=elldash*p;
	n:=Floor(((p+1)/(p-1))*(m+1));	 
	mdash:=m + Ceiling(n/(p+1));
	
	// Steps 2 and 3

	e,Ep1:=HigherLevelKatzExp(N,p,k0,m,mdash,n,elldash,elldashp,weightbound); 

	ell:=Dimension(Parent(Transpose(e)[1]));
	S:=Parent(e[1,1]);

	// Step 4

	q := Parent(Ep1).1; 
	Ep1p := Evaluate(Ep1,q^p);
	Ep1pinv := Ep1p^-1;
	G := Ep1*Ep1pinv;
	Aseq:=[];
	
	for k in kseq do
		kdiv:=k div (p-1);
		Gkdiv := G^kdiv;

		u:=Parent(e)!0; // ell x elldashp zero matrix.
	
		for i:=1 to ell do
			ei:=Parent(Gkdiv)!0;
			for j:=1 to elldashp do // extract rows of a as series
				ei:=ei + e[i,j]*q^(j-1);
			end for;
			Gkdivei:=Gkdiv*ei; // act by G^kdiv
			for j:=1 to elldashp do // put back as rows of ak
				u[i,j]:=Coefficient(Gkdivei,j-1);
			end for;
		end for;

		// Step 5

		T:=ZeroMatrix(S,ell,elldash);
	
		for i:=1 to ell do
			for j:=1 to elldash do
				T[i,j]:=u[i,p*(j-1) + 1];
			end for;
		end for;
	
		// Step 6: Solve T = AE for A.

		A := ZeroMatrix(S,ell,ell);
	
		for i := 1 to ell do
			Ti := T[i];		
			for j := 1 to ell do
				ej := Parent(Ti)![e[j,l]: l in [1 .. elldash]];
				ejleadpos:=LeadingPosition(ej);
				lj:=Integers()!ej[ejleadpos];
				A[i,j] := S!((Integers()!Ti[ejleadpos])/lj);
				Ti := Ti - A[i,j]*ej;
			end for;
		end for;
		
		Append(~Aseq,MatrixRing(IntegerRing(p^m),ell)!A);
		
	end for;
		
	return Aseq;


end function;

//  *** LEVEL 1 ***

// Returns dimension of space of modular forms of weight k and level 1.

function DimensionMk(k)

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

// Returns basis for W_i (those elements in the Miller basis of weight k which 
// are not in E_(p-1) x {weight (k - (p-1)) forms} and a power of delta
// which can be reused on the next call of function.

function ComputeWi(k,p,delta,deltaj,E4,E6)
	
	// Define a and b
	a := k mod 3;
	b := (k div 2) mod 2;
		
	// Compute dimensions required for Miller basis
	d := DimensionMk(k) - 1;
	e := DimensionMk(k - (p-1)) - 1;
	
	// Construct basis for Wi
	Wi := [];
	for j := e+1 to d do
		// compute aj = delta^j*E6^(2*(d-j) + b)*E4^a
		aj := deltaj*E6^(2*(d-j) + b)*E4^a;
		deltaj := deltaj*delta;
		Wi := Append(Wi,aj);
	end for;

	return Wi,deltaj;

end function;

// AUXILIARY CODE: KATZ EXPANSIONS

// Returns list e of Katz expansions e_(i,s) from Step 3 of Algorithm 1
// and E_(p-1) for use in Step 4.

function KatzExpansions(k0,p,ellp,mdash,n)
	
	S := IntegerRing(p^mdash); // See Footnote (1) below
	Ep1 := ESeries(p-1,ellp,S);

	E4 := ESeries(4,ellp,S);
	E6 := ESeries(6,ellp,S);
	q := Parent(E4).1;
	delta := Delta(q);
	
	deltaj := Parent(delta)!1;
	e := [];	
	for i := 0 to n do
		Wi,deltaj := ComputeWi(k0 + i*(p-1),p,delta,deltaj,E4,E6);
		for bis in Wi do
			eis := p^Floor(i/(p+1))*Ep1^(-i)*bis;
			e := Append(e,eis);
		end for;
	end for;
	
	return e,Ep1;

end function;	

// MAIN FUNCTIONS

// Returns matrix A modulo p^m from Step 6 of Algorithm 1 for each k on kseq.
// kseq has weights congruent modulo (p-1).

// Notational change from paper: In Step 1 following Wan we defined j by
// k = k_0 + j(p-1) with 0 <= k_0 < p-1. Here we replace j by kdiv so that
// we may use j as a column index for matrices.

function Level1UpGj(p,kseq,m) 
 
	// Step 1

	k0 := kseq[1] mod (p-1);
	n := Floor(((p+1)/(p-1)) * (m+1));
	ell := DimensionMk(k0 + n*(p-1));
	ellp := ell*p;
	mdash := m + Ceiling(n/(p+1));

	// Steps 2 and 3

	e,Ep1 := KatzExpansions(k0,p,ellp,mdash,n);
	
	// Step 4

	q := Parent(Ep1).1; 
	Ep1p := Evaluate(Ep1,q^p);
	Ep1pinv := Ep1p^-1;
	G := Ep1*Ep1pinv;
	Aseq:=[];
	
	for k in kseq do
		kdiv := k div (p-1);
		Gkdiv := G^kdiv;
		u := [];
		for i := 1 to ell do
			ei := e[i];
			ui := Gkdiv*ei;
			u := Append(u,ui);
		end for;
	
		// Step 5 and computation of T in Step 6

		S := Parent(Coefficient(e[1],0));
		T := ZeroMatrix(S,ell,ell);
	
		for i := 1 to ell do
			for j := 1 to ell do
				T[i,j] := Coefficient(u[i],p*(j-1));
			end for;
		end for;
	
		// Step 6: solve T = AE using fact E is upper triangular.
		// Warning: assumes that T = AE (rather than pT = AE) has 
		// a solution over Z/(p^mdash). This has always been the case in 
		// examples computed by the author, see Note 3.1.

		A := ZeroMatrix(S,ell,ell);
	
		for i := 1 to ell do
			Ti := T[i];		
			for j := 1 to ell do
				ej := Parent(Ti)![Coefficient(e[j],l-1): l in [1 .. ell]];
				lj := Integers()!ej[j];
				A[i,j] := S!((Integers()!Ti[j])/lj);
				Ti := Ti - A[i,j]*ej;
			end for;
		end for;			

		// Append A mod p^m to Aseq.
		
		Append(~Aseq,MatrixRing(IntegerRing(p^m),ell)!A);

	end for;

	return Aseq;

end function;

//  *** MAIN CODE FOR GENERAL LEVEL ***:

// Returns matrix A modulo p^m from Step 6 of Algorithm 1 (N = 1) or
// Algorithm 2 (N > 1).

function UpGj(p,N,kseq,m,weightbound)

	if N gt 1 then
		return HigherLevelUpGj(p,N,kseq,m,weightbound);
	else
		return Level1UpGj(p,kseq,m);
	end if;

end function;

// Returns reverse characteristic series modulo mod p^m of the U_p 
// operator on the space of p-adic overconvergent modular forms of level N and 
// weight k, for each k in kseq.  
// The optional parameter weightbound is explained in the preamble.

function HeckeSeries(p,N,kseq,m: weightbound := 6)

    oneweight:=false;
    // Convert single weight to list
    if Type(kseq) eq RngIntElt then
        kseq:=[kseq];
        oneweight:=true;
    end if;

	
	// The algorithm may terminate with false output without the following check:
	assert IsValidWeightSequence(kseq,p); // Verify klist is a valid input
	assert p ge 5; // check p >= 5
	assert ((N mod p) ne 0); // p does not divide N
	
	// For list of odd weights return all 1s sequence
	if IsOdd(kseq[1]) then
		return [1: i in [1 .. #kseq]];
	end if;
	
	Zpmt<t>:=PolynomialRing(pAdicRing(p,m));
	Aseq:=UpGj(p,N,kseq,m,weightbound);
	Pseq:=[];
	for A in Aseq do
		P:=ReverseCharacteristicPolynomial(A); // P is over IntegerRing(p^m)
		Append(~Pseq,Zpmt!P); 
	end for;

    if oneweight eq true then
        return Pseq[1];
    else
        return Pseq;
    end if;
    
end function;




