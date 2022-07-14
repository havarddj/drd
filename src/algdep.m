// Common structures:
ZZ := Integers();
QQ := Rationals(); 
RR := RealField(500);

function nonp_Height(P,p)
    /* return height of polynomial up to powers of p */
    return Max([Abs(c/p^Valuation(c,p)) : c in Coefficients(P)]);
end function;


function IsPowerofP(a,p : n :=20)
    for j in [0..n] do
	if ZZ!(a) eq ZZ!(p^j) then
	    return true;
	end if;
    end for;
    return false;
end function;			    

		    
function algdepZpm(a,deg)

	N  := Modulus(Parent(a));
	RR := RealField(500);
	M  := ZeroMatrix(RR,deg+2,deg+2);

	for i:=0 to deg do
		M[i+1,1] := ZZ!((a)^i);
	end for;
	M[deg+2][1] := N;

	for j:=1 to deg+1 do
		M[j,j+1] := 1;
	end for;

	Y,T := LLL(M);

	PolZ<t> := PolynomialRing(ZZ);
	P       := Floor(Y[2][1] - Y[2][2]);
	for j := 3 to deg+2 do
		P := P - Floor(Y[2][j])*t^(j-2);
	end for;

	return P;

end function;

// Algebraic recognition for element in Qp.
function algdepQp(a,deg)
    
    PolZ<x>:=PolynomialRing(ZZ);
   
    p := Prime(Parent(a));
    m := Precision(Parent(a));
    N := p^m;

    M:=ZeroMatrix(RR,deg+2,deg+2);
    for j := 1 to deg+1 do 
        M[j,j] := 1;
        M[j,deg+2] := QQ!(a^(j-1));
    end for;
    M[deg+2][deg+2] := N;
    Y,T:=LLL(M);

    P1 := Floor(Y[2][deg+2] - Y[2][1]);
    for j := 2 to deg+1 do
        P1 := P1 - Floor(Y[2][j])*x^(j-1);
    end for;
    /* Fac1 := Factorisation(P1); */
    /* P1   := Fac1[#Fac1][1]; */
    
    return P1;
       
end function;

// Algebraic recognition for element in Qp^2.
function algdepQp2(a,deg)

    PolZ<x>:=PolynomialRing(ZZ);
   
    p := Prime(Parent(a));
    m := Precision(Parent(a));
    N := p^Floor(5*m/7);

    M:=ZeroMatrix(RR,deg+3,deg+3);
    for j := 1 to deg+1 do 
        M[j,j] := 1;
        M[j,deg+2] := QQ!(Coefficient((a)^(j-1),1));
        M[j,deg+3] := QQ!(Coefficient((a)^(j-1),2));
    end for;
    M[deg+2][deg+2] := N;
    M[deg+3][deg+3] := N;
    Y,T:=LLL(M);

    P1 := Floor(Y[2][deg+2] - Y[2][1]);
    for j := 2 to deg+1 do
        P1 := P1 - Floor(Y[2][j])*x^(j-1);
    end for;
    /* Fac1 := Factorisation(P1); */
    /* P1   := Fac1[#Fac1][1]; */
    
    return P1;
       
end function;


// Given a number a, attempt to recognise it as an algebraic number.
function algdep(a,deg)
	
	if Type(a) eq RngIntResElt then
		return algdepZpm(a,deg);
	else
		if Degree(Parent(a)) eq 1 then
			return algdepQp(a,deg);
		else
			return algdepQp2(a,deg);
		end if;
	end if;	

end function;


function recAlgdepQp(a,deg)
    PolZ<x>:=PolynomialRing(ZZ);
   
    p := Prime(Parent(a));
    m := Precision(Parent(a));
    N := 10^600;
    assert deg mod 2 eq 0;
    d := ZZ!(deg/2);
    M:=ZeroMatrix(RR,d+2,d+2);
    for j := 0 to d do 
        M[j+1,j+1] := 1;
	if j eq d then
	    M[j+1,d+2] := QQ!(a^j);
	else    
            M[j+1,d+2] := QQ!(a^j + a^(deg - j));
	end if;
    end for;
    M[d+2][d+2] := N;
    Y,T:=LLL(M);
    /* print "Y equals", Y[1], Y[2]; */

    P1 := -Floor(Y[1][d+1])*x^d;
    for j := 0 to d-1 do
	c := Floor(Y[1][j+1]);
	P1 := P1 - c*(x^j + x^(deg-j));	
    end for;
    /* Fac1 := Factorisation(P1); */
    /* P1   := Fac1[#Fac1][1]; */
    
    return P1;
end function;


function recAlgdepQp2(a,deg)
    /* Note: this is not that good; for Phi := CyclotomicPolynomial(7^2-1), we
     don't find the right one with precision 400. :,<*/
    /* Let deg = 2d. */
    /* We want to find a degree d polynomial P = b_0 + b_1x+ ... + b_d
     x^d which satisfies b_0(a^0 + a^2d) + b_1(a^1+a^2d-1)+ ... +
     b_d-1(a^d-1 + a^d+1) + b_d(a^d) = 0.  This gives a reciprocal
     polynomial for which a is a root. */
    RR := RealField(500);

    PolZ<x>:=PolynomialRing(ZZ);

    p := Prime(Parent(a));
    m := Precision(Parent(a));
    /* N := p^Floor(5*m/7); */

    N := p^m;


    /* N := p^m; */

    assert deg mod 2 eq 0;

    d := ZZ!(deg/2);
    
    M := ZeroMatrix(RR,d+3,d+3);
    /* More intuitive to loop from j=0 */
    for j := 0 to d do 
        M[j+1,j+1] := 1;	/* but of course indexing starts at 1 in magma */
	if j eq d then
	    ci := a^d;
	else
	    ci := a^j + a^(deg-j);
	end if;
	
        M[j+1,d+2] := QQ!(Coefficient(ci,1));
        M[j+1,d+3] := QQ!(Coefficient(ci,2));
    end for;
    M[d+2][d+2] := N;
    M[d+3][d+3] := N;

    Y,T:=LLL(M);

    /* print "Y is given by", Y[1], Y[2], Y[3]; */

    /* P1 := Floor(Y[1][d+2] - Y[1][1])*(1+x^deg); */
    P1 := -Floor(Y[1][d+1])*x^d;
    for j := 0 to d-1 do
	c := Floor(Y[1][j+1]);
	P1 := P1 - c*(x^j + x^(deg-j));
    end for;

    return P1;

    /* print "P1 is",P1; */
    /* if Valuation(Evaluate(P1,a)) gt Floor(4*m/7) then */
    /*     return P1; */
    /* else */
    /*     return 10^200*x^deg; */
    /* end if; */
    
end function;

function recAlgdep(a,deg)	
    if Type(a) eq RngIntResElt then
	return algdepZpm(a,deg);
    else
	if Degree(Parent(a)) eq 1 then
	    print "running recAlgdepQp";
	    return recAlgdepQp(a,deg);
	else
	    print "running recAlgdepQp2";
	    return recAlgdepQp2(a,deg);
	end if;
    end if;

end function;


function IsReciprocal(P)
    d := Degree(P);
    for i := 0 to d do 		/* no need to optimize and take Floor(d/2) */
	if not Coefficient(P,i) eq Coefficient(P,d-i) then
	    return false;
	end if;

    end for;
    return true;
end function;
/* function GSAlgdep(a,deg, pval) */
/*     /\* Input: */
/*        - a, approximation to Gross-Stark unit u in Qp^2, whose */
/*           "renormalised minimal " poln P over Q */
/*           is the (desired) output. P will be reciprocal */
/*        - the desired degree of P (although it could end up being smaller) */
/*        - pval, the ord_p of the constant term (and hence also the leading term) */
/*    *\/ */

/*     /\* Important! Input Exp(CT), not CT! *\/ */
/*     /\* Håvard 21/01/22: added check for reciprocality *\/ */
/*     /\* 25/01/22: wrote recAlgdep functions which apply LLL to find reciprocal pols*\/ */
/*     /\* Håvard 08/04/22: rewrote to make use of known constant terms  *\/ */
/*     /\* Håvard 17/06/22: fix pval stuff *\/ */
/*     /\* Test: */
/*     p := 7; */
/*     Kp := UnramifiedExtension(pAdicField(p,50),2); */
/*     RKp<x> := PolynomialRing(Kp); */
/*     a := Roots(Phi,Kp)[1][1]/p^2; */
/*    *\/ */
/*     /\* deg := 2*deg; *\/ */
/*     Kp   := Parent(a); */
/*     assert #Eltseq(a) eq 2; */
/*     p    := Prime(Kp); */
/*     m    := Precision(Parent(a)); */
/*     RKp<z> := PolynomialRing(Kp); */
/*     zeta := Roots(RKp!CyclotomicPolynomial(p^2-1))[1][1]; */
    
/*     ZZ := Integers(); */
/*     QQ := Rationals(); */
   
/*     PolZ<x> := PolynomialRing(ZZ); */
/*     PolQ<x> := PolynomialRing(QQ); */
/*     RR := RealField(500); */
/*     N := ZZ!(p^m); */

    
/*     /\* as in the real case, we can try to weight by a (large) factor. However, */
/*      to avoid trouble with 2 or 5, we should probably make this a high power of a prime != p *\/ */
/*     /\* MBig := NextPrime(p)^(Floor(m + Log(p))); *\/ */
/*     if p eq 2 then */
/* 	q := 3; */
/*     else */
/* 	q := 2; */
/*     end if; */
/*     MBig := q^Floor(m + Log(p)); */
/*     P := PolZ!MBig*x^deg; */
/*     Q := P; 			/\* the polynomial we will return *\/ */
/*     assert deg mod 2 eq 0; */
/*     d := ZZ!(deg/2); */
    
/*     for k := 0 to p^2-1 do */
/* 	azk := a*zeta^k; */
/* 	print "a times root of unity equals ", azk; */

/* 	M := ZeroMatrix(RR,d+3,d+3); */
	
/* 	/\*  |---- d+1 ----| */
/* 	   [ 1, 0, ... , 0, Mbig*(p^pval*(1+a^deg))_1, Mbig*(p^pval*(1+a^deg))_2 */
/* 	     0, 1, ... , 0, Mbig*(a^1 + a^deg-1)_1, Mbig*(a^1+a^deg-1)_2 */
/* 	     0, 0, ... , 0, Mbig*(a^2 + a^deg-2)_1, Mbig*(a^2+a^deg-2)_2 */
/* 	...  */
	    
/* 	    0, 0, ... , 1, Mbig*(a^d)_1,            Mbig*(a^d)_2 */
/* 	    0, 0, ... , 0, Mbig*p^BIG,              0, */
/* 	    0, 0, ... , 0, 0,                  Mbig*p^BIG]  	*\/ */
/* 	/\* M[1,1] := 1;		/\\* insert a_0 manually *\\/ *\/ */
/* 	/\* ci := 1+azk^d; *\/ */
/* 	/\* M[1,d+2] := MBig*p^pval *Floor(QQ!Coefficient(ci,1));	/\\* note: M[1][d+3] = 0  *\\/ *\/ */
/* 	/\* M[1,d+3] := MBig*p^pval *Floor(QQ!Coefficient(ci,1)); *\/ */
/* 	/\* print "looking for polynomial with constant term", p^pval; *\/ */
/* 	for j := 0 to d do 	/\* terms a_1, ... , a_d *\/ */
/*             M[j+1,j+1] := 1;	 */
/* 	    if j eq d then */
/* 		ci := azk^j; */
/* 	    else */
/* 		ci := (azk^j + azk^(deg-j)); */
/* 	    end if; */
	    
/*             M[j+1,d+2] := MBig*Floor(QQ!(Coefficient(ci,1))); */
/*             M[j+1,d+3] := MBig*Floor(QQ!(Coefficient(ci,2))); */
/* 	end for; */
/* 	M[1,d+2] := p^pval*M[1,d+2]; */
/* 	M[1,d+3] := p^pval*M[1,d+3]; */
/* 	/\* we add the following because we don't necessarily need the */
/* 	linear combo to be zero, just very close to a high power of p */
/*        *\/ */
/* 	M[d+2][d+2] := MBig*N; */
/* 	M[d+3][d+3] := MBig*N; */
/* 	/\* print "d = ", d; *\/ */
/* 	/\* print "M = ", M; *\/ */
/* 	B,T := LLL(M); */

/* 	/\* print "Short vectors equal", B[1], B[2], B[3]; *\/ */
/* 	/\* try to intelligently pick right soln vector: *\/ */
/* 	j := 1; */
/* 	for n in [1..4] do */
/* 	    if B[n][1] eq 1 then */
/* 		j := n; */
/* 	    end if; */
/* 	end for; */
/* 	/\* j := 1;	 /\\* pick soln vector *\\/ *\/ */
/* 	/\* print "Soln vector,", B[j]; *\/ */

/* /\* Floor(Y[2][deg+2] - Y[2][1]); *\/ */
/* 	P1 := Floor(B[j][d+1])*x^d; /\* start with the middle coeff *\/ */
/* 	/\* then add top and bottom, since these are adjusted by p-valuation from Meyer: *\/ */
/* 	P1 := P1 + Floor(B[j][1])*p^pval*(1+x^deg); */
/* 	/\* then do the rest *\/ */
/* 	for j := 1 to d-1 do */
/* 	    aj := Floor(B[j][j+1]); */
/* 	    P1 := P1 + aj*(x^j + x^(deg-j)); */
/* 	end for; */

/* 	P := PolZ!P1; */
/* 	if Coefficient(P,Degree(P)) lt 0 then */
/* 	    P := -P; */
/* 	end if; */
/* 	P := PolZ!((PolQ!P)/GCD(Coefficients(P))); */
/* 	if Coefficient(P,0) eq p^pval then */
/* 	    print "found good candidate"; */
/* 	    print "factorisation of disc:"; */
/* 	    Factorization(Discriminant(P)); */
/* 	    return P; */
/* 	end if; */
/* 	print "k = ", k, "P = ", P; */
/* 	if nonp_Height(P,ZZ!p) le nonp_Height(Q,ZZ!p) then */
/* 	    Q := P; */
/* 	end if; */

/*     end for;    */
/*     return P; */
    
/* end function; */


function ThoroughAlgdep(a,deg : nn:= 10)

    Kp   := Parent(a);
    assert #Eltseq(a) eq 2;
    p    := Prime(Kp);
    m    := Precision(Parent(a));
    RKp<z> := PolynomialRing(Kp);
    zeta := Roots(RKp!CyclotomicPolynomial(p^2-1))[1][1];
    
    ZZ := Integers();
    QQ := Rationals();
   
    PolZ<x> := PolynomialRing(ZZ);
    PolQ<x> := PolynomialRing(QQ);
    
    P := PolZ!(10^100*x^deg);

    for k := 0 to p^2-1 do
	
	P1 := recAlgdep(a*zeta^k,deg);
	/* print P1; */
	/* if IsReciprocal(P1) then */
	/*     print " found reciprocal polynomial!"; */
	/*     P := P1; */
	/* end if; */

    end for;
    if not IsIrreducible(P) then
	Fac1 := Factorisation(P);
	P   := Fac1[#Fac1][1];
    end if;
    if Coefficient(P,Degree(P)) lt 0 then
	P := -P;
    end if;
    P := P/GCD(Coefficients(P));
    return P;

end function;

function Rlindep(L)
    /* looks for integral linear dependence between elements of vector L*/

    N := 10^6;			/* random big param. */
    /* N := 1; */
    d := #L;
    M := ZeroMatrix(RR,d,d+1);

    for j := 1 to d do 
        M[j,j] := 1;
	/* print RR!(L[j]); */
	M[j,d+1] := RR!(L[j]*N);
    end for;
    /* print M, Parent(M); */
    B,T:=LLL(M); /* returns basis B, linear transformation T */

    
    ni_list := [];
    for i in [1..d] do
	Append(~ni_list, B[1][i]);
    end for;
    /* print "Integer coeffs = ", ni_list; */
    print "B = ", B;
    print "delta: ", &+[ni_list[i]*L[i] : i in [1..d] ]; 
    return ni_list;
    
end function;



function GenusFieldRootsOf1(D)
    m := SquarefreeFactorization(D);
    if m mod 4 eq 1 then
	disc := m;
    else
	disc := 4*m;
    end if;
    e := 2;
    for fac in Factorisation(disc) do
	p := fac[1];
	if p eq 2 and m mod 4 eq 3 then
	    e := e*2;
	end if;
	if p eq 3 then
	    e := e*3;

	end if;

    end for;

    return e;
end function;

function roots_mod_p2(f,D,p)
    R<x> := PolynomialRing(ZZ);
    f := R!f;
    F := NumberField(x^2-D);

    K := Completion(F,p*Integers(F));
    k,red := ResidueClassField(Integers(K));
    red_list := [red(l[1]/p^Valuation(l[1])) : l in Roots(f,K)];
    for x in red_list do
	print "root mod p^2 equals", x, "of order", Order(x);
    end for;
    return red_list;
end function;


function partialSum(Lvals)
    pos_vals := [];
    for i in [1..#Lvals] do
	if Lvals[i] ge 0 then
	    Append(~pos_vals, Lvals[i]);
	end if;
    end for;

    pos_vals := Sort(pos_vals);

    partial_sums := [];
    sum := 0;
    for i in [1..#pos_vals] do
	sum := sum + pos_vals[i];
	Append(~partial_sums,sum);
    end for;
    return partial_sums;
end function;

function GSAlgdep(a,deg,Lvals : D :=1)
    /* Let deg = 2d. */
    /* We want to find a degree d polynomial P = b_0 + b_1x+ ... + b_d
     x^d which satisfies b_0(a^0 + a^2d) + b_1(a^1+a^2d-1)+ ... +
     b_d-1(a^d-1 + a^d+1) + b_d(a^d) = 0.  This gives a reciprocal
     polynomial for which a is a root. */
    RR := RealField(500);

    PolZ<x>:=PolynomialRing(ZZ);
    PolQ<x>:=PolynomialRing(QQ);
    P := PolZ!(10^100)*x^deg;
    p := Prime(Parent(a));
    m := Floor(Precision(a)-2*Log(p));
    N := p^Floor(5*m/7);
    /* N := p^m; */
    RKp := PolynomialRing(Parent(a));
    zeta := Roots(RKp!CyclotomicPolynomial(p^2-1))[1][1];
    /* N := p^m; */
    partial_sums := Reverse(partialSum(Lvals));

    assert deg mod 2 eq 0;
    
    d := ZZ!(deg/2);

    for k := 0 to p^2-1 do
	b := a*zeta^k;
	
	M := ZeroMatrix(RR,d+3,d+3);
	/* More intuitive to loop from j=0 */
	
	for j := 0 to d do 
            M[j+1,j+1] := 1;	/* but of course indexing starts at 1 in magma */
	    if j eq d then
		cj := b^d;
	    else 
		cj := QQ!(p^(partial_sums[j+1])) *(b^j + b^(deg-j));
	    end if;
	    
            M[j+1,d+2] := QQ!(Coefficient(cj,1));
            M[j+1,d+3] := QQ!(Coefficient(cj,2));
	end for;
	M[d+2][d+2] := N;
	M[d+3][d+3] := N;

	Y,T:=LLL(M);
	/* print "Y is given by", Y[1], Y[2], Y[3]; */
	/* P1 := Floor(Y[1][d+2] - Y[1][1])*(1+x^deg); */
	P1 := -Floor(Y[1][d+1])*x^d;
	for j := 0 to d-1 do
	    c := Floor(Y[1][j+1]);
	    P1 := P1 - QQ!(p^partial_sums[j+1])*c*(x^j + x^(deg-j));
	end for;
	print "P1 = ", P1, "\na_0 = ", Factorisation(Max(Abs(ZZ!Coefficient(P1,0)),1)), "\n";
	
	if Coefficient(P1,Degree(P1)) lt 0 then
	    P1 := -P1;
	end if;
	P1 := PolZ!((PolQ!P1)/GCD(Coefficients(PolZ!P1)));
	
	/* print P1; */

	/* if (nonp_Height(P1,p) le nonp_Height(P,p)) and (ZZ!Discriminant(P) mod D eq 0) then */
	if IsPowerofP(Coefficient(P1,0),p) and Coefficient(P1,d) ne 0 then
	    P := P1;
	end if;
    /* Fac1 := Factorisation(P1); */
    /* P1   := Fac1[#Fac1][1]; */
    end for;



    if P eq PolZ!(10^100)*x^deg then
	return 0;
    end if;
    return P;

end function;
