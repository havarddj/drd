IMat := Matrix(2,2,[[1, 0],[0,1]]);  // Identity
SMat := Matrix(2,2,[[0,-1],[1,0]]);  // Order 4
TMat := Matrix(2,2,[[1, 1],[0,1]]);  // Translation
STMat:= Matrix(2,2,[[0,-1],[1,1]]);  // Order 6

/* Helper functions */
/*  */
/*  */
/*  */

// Return the gcd of the coefficients of a quadratic form.
function GcdForm(Q)

	return Gcd(Gcd(Q[1],Q[2]),Q[3]);
	
end function; 


// Check whether a form is primitive.
function IsPrimitiveForm(Q)

	return GcdForm(Q) eq 1;

end function;


// Check whether a given 2x2 matrix 'g' is integral
function IsIntegralMatrix(g)

	d := Degree(Parent(g));
	return [IsIntegral(g[i,j]) : i,j in [1..d]] eq [true : i,j in [1..d]];

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


// Check whether pair1 = (w1, delta1) and pair2 = (w2, delta2) are equivalent in RM(n,C)
function EquivalenceRM(pair1,pair2)

	boo := false;
	w1  := pair1[1];
	w2  := pair2[1];
	delta1 := pair1[2];
	delta2 := pair2[2];
	equiv, gamma := IsEquivalent(w1,w2);
	if equiv then
		delta2 := ChangeRing(delta2,Rationals());
		boo := IsIntegralMatrix(delta1*gamma*delta2^(-1));
		/* w1, "is equiv/Q to", w2; */
		/* "matrix of equiv = ", delta1*gamma*delta2^(-1); */
	end if;
	
	return boo;

end function;


// Given F, this function returns all SL_2(Z)-translates Q' of Q or Qinv that are separated by 0.
// This means that one of the roots of Q' is less than 0, and the other is greater than 0.
function NearlyReducedForms(F)
 
    F0 := ReducedForm(F);
    /* As_p := [];  // Positive a's */
    /* As_m := [];  // Negative a's */
    Fs_p := [];  // All forms with positive a
    Fs_m := [];  // All forms with negative a
    Fs := [];
    F  := F0;
    started := false;
    while F ne F0 or started eq false do
 	started := true;
 	a := F[1];
 	b := F[2];
 	c := F[3];
	/* print F; */
 	F := ReductionStep(F);
 	s := Abs(ZZ!((b+F[2])/(2*c))); // The quantity 's' from section 6.4 in Buchmann-Vollmer
	/* print s; */
 	if a gt 0 then
 	    for i := 1 to s do
 		A := a+i*b+i^2*c;
		B := b + 2*i*c;
		C := c;
 		Append(~Fs_p,[A,B,C]);
 		Append(~Fs_m,[C,-B,A]);
		Append(~Fs,[A,B,C]);
		//print "Added ", A,b+2*i*c,c;
		//assert (b+2*i*c)^2 - 4*A*c eq Discriminant(F);  // REMOVE !!!
 	    end for;
 	end if;
 	if a lt 0 then
 	    for i := 1 to s do
		A := c;
		B := -b+2*i*c;
		C := a-i*b+i^2*c;
 		Append(~Fs_p,[A,B,C]);
 		Append(~Fs_m,[C,-B,A]);
		Append(~Fs,[A,B,C]);
		//print "Added ", c,-b+2*i*c,a-i*b+i^2*c;
		//assert (-b+2*i*c)^2-4*c*(a-i*b+i^2*c) eq Discriminant(F); // REMOVE !!!
 	    end for;
 	end if;
    end while;
    
    return Fs_p, Fs_m, Fs;
    
end function;


// Given an integer n>0, return the matrices that define the Hecke operator T_n in level N.
function HeckeMatrices(n : N := 1)

	Sd := [d : d in Divisors(n) | GreatestCommonDivisor(ZZ!(n/d),N) eq 1];
	Mn := [];
	for d in Sd do
	    for j := 0 to d-1 do
		Append(~Mn,Matrix([[d,j],[0,ZZ!(n/d)]]));
	    end for;
	end for;
	
	return Mn;

end function;


// This function computes the set RM+-(n,C) for a fixed ideal class C, using Hecke operators on quadratic forms. 
// The computation relies on a set of representatives Forms_d of the classes in RM+-(n,C) for d a large divisor of n.
function RM_Points(n,d,Forms_d : D := ZZ!(Discriminant(Forms_d[1][1])/d^2))
    Mn      := HeckeMatrices(ZZ!(n/d) : N := 1); // Hecke operator in level 1!
    Forms_n := [];
    F_pos_n := [];
    F_neg_n := [];
    Fs_n := [];
    Fs := [];
    /* print "number of Hecke matrices=", #Mn; */
    for pair in Forms_d do
 	a := pair[1][1];
 	b := pair[1][2];
 	c := pair[1][3];
  	delta_d := pair[2];
 	for Mat in Mn do
 	    // Matrix coefficients;
 	    q := Mat[1,1];
 	    r := Mat[1,2];
 	    s := Mat[2,1];
 	    t := Mat[2,2];
 	    // Action of M2(Z), uses the fact that s=0 for these Hecke representatives!! 
 	    A  :=   q^2*a;
 	    B  := 2*q*r*a + ZZ!(n/d)*b;
 	    C  :=   r^2*a + r*t*b + t^2*c;
 	    MF := QuadraticForms(D*n^2)!<A,B,C>;
 	    delta_n := delta_d*Mat;
 	    RM_n := [* MF,delta_n *];
 	    if [EquivalenceRM(RM_n,G) : G in Forms_n] eq [false : G in Forms_n] then
 		Fs_p, Fs_m, Fs  := NearlyReducedForms(MF);
		F_pos_n := F_pos_n cat Fs_p;
		F_neg_n := F_neg_n cat Fs_m;
		Fs_n := Fs_n cat Fs;
		/* Mat, MF, As_p, " "; */
		
 		Append(~Forms_n,RM_n);
 	    end if;
 	end for;
    end for;
    
    return F_pos_n, F_neg_n, Forms_n;
 
end function;



/* Diagonal restrictions  */
/*  */
/*  */
/*  */

// Computes the nearly reduced forms for the first m coefficients of the diagonal restriction.
function Diagonal_Restriction_data(F,m) // weight 2k

	// Initial values:
	F_p,F_n,Forms_0 := RM_Points(1,1,[[*F,IMat*]]);
	Forms := [Forms_0];
	Fs    := [[F_p,F_n]];
	// Hecke operators
	for n := 2 to m-1 do
	    Diag_F_n := 0;
	    if n eq 1 then
		p := 1;
		d := 1;
	    else
 		p := PrimeDivisors(n)[1]; // Smallest prime divisor of n.
 		d := ZZ!(n/p^(Valuation(n,p)));
 	    end if;
	    F_pos_n, F_neg_n, Forms_n := RM_Points(n,d,Forms[d]);
	    Append(~Fs, [F_pos_n, F_neg_n]);
   	    Append(~Forms, Forms_n);
   	end for;
   	
   	return Fs, Forms;
   	
end function;

function diagonal_restriction_derivative(F,p,m,Fs,Forms : pprec := m)
    /* m = number of terms, pprec = p-adic precision */
    Rp<s>  := UnramifiedExtension(pAdicRing(p,pprec),2);
    R<q>   := PowerSeriesRing(Rp,m);

    Diag_F := R!0;
    f := Conductor(Parent(F));    
    sqrtD := Rp!Sqrt(Rp!Discriminant(F));

    for n in [1..m-1] do
	Fs_pos_n := Fs[n][1];
	Fs_neg_n := Fs[n][2];
	prod_n := 1;
	for i := 1 to #Fs_pos_n do
	    // Positive
	    Fi := Fs_pos_n[i];
	    a := Fi[1];
	    b := Fi[2];
	    c := Fi[3]; 
	    if Gcd(a,p*f) eq 1 then
		fac := Rp!((-b + n*sqrtD)/(2*a));
		prod_n := prod_n*fac;
	    end if;
	    // Negative
	    Fi := Fs_neg_n[i];
	    a := Fi[1];
	    b := Fi[2];
	    c := Fi[3]; 
	    if Gcd(a,p*f) eq 1 then
		fac := Rp!((-b + n*sqrtD)/(2*a));
		prod_n := prod_n/fac;
	    end if;
	end for;
	coeff_n := Rp!(Log(prod_n/p^Valuation(prod_n)));
	Diag_F := Diag_F + 2*coeff_n*q^n;
    end for;

    ct := IsOverconvergent(Diag_F : prt := true);
    print ct;
    return R!ct + Diag_F;

end function;	  


function Diagonal_Restriction_Derivative(F,p,m : pprec := m)
    
    Fs, Forms := Diagonal_Restriction_data(F,m);
    /* print Fs[2]; */
    return diagonal_restriction_derivative(F,p,m,Fs,Forms : pprec := pprec);
	
end function;



