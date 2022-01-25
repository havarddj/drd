// Common structures:
ZZ := Integers();
QQ := Rationals(); 
RR := RealField(500);

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
    Fac1 := Factorisation(P1);
    P1   := Fac1[#Fac1][1];
    
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
    Fac1 := Factorisation(P1);
    P1   := Fac1[#Fac1][1];
    
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
    N := p^m;
    assert deg mod 2 eq 0;
    d := deg/2;
    M:=ZeroMatrix(RR,d+2,d+2);
    for j := 1 to d+1 do 
        M[j,j] := 1;
        M[j,deg+2] := QQ!(a^(j-1) + a^(deg - j+1));
    end for;
    M[deg+2][deg+2] := N;
    Y,T:=LLL(M);

    P1 := Floor(Y[2][deg+2]/2 - Y[2][1]/2)*(1+x^deg);
    for j := 2 to deg+1 do
        P1 := P1 - Floor(Y[2][j])*(x^(j-1)+x^(deg-j+1));
    end for;
    /* Fac1 := Factorisation(P1); */
    /* P1   := Fac1[#Fac1][1]; */
    
    return P1;    
end function;


function recAlgdepQp2(a,deg)

    RR := RealField(500);    
    assert deg mod 2 eq 0;
    PolZ<x>:=PolynomialRing(ZZ);

    p := Prime(Parent(a));
    m := Precision(Parent(a));
    N := p^Floor(5*m/7);

    d := ZZ!(deg/2);
    
    M:=ZeroMatrix(RR,d+3,d+3);
    for j := 1 to d+1 do 
        M[j,j] := 1;
	ci := a^(j-1) + a^(deg-j+1);
        M[j,d+2] := QQ!(Coefficient(ci,1));
        M[j,d+3] := QQ!(Coefficient(ci,2));
    end for;
    M[d+2][d+2] := N;
    M[d+3][d+3] := N;
    Y,T:=LLL(M);

    P1 := Floor(Y[2][d+2]/2 - Y[2][1]/2)*(1+x^deg);
    for j := 2 to d+1 do
        P1 := P1 - Floor(Y[2][j]/2)*(x^(j-1) + x^(deg-j+1));
    end for;
    /* Fac1 := Factorisation(P1); */
    /* P1   := Fac1[#Fac1][1]; */
    
    return P1;
end function;

function recAlgdep(a,deg)	
    if Type(a) eq RngIntResElt then
	return algdepZpm(a,deg);
    else
	if Degree(Parent(a)) eq 1 then
	    return recAlgdepQp(a,deg);
	else
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

function ThoroughAlgdep(a,deg : nn := 100)
    /* Important! Input Exp(CT), not CT! */

    /* Håvard 21/01/22: added check for reciprocality */
    /* 25/01/22: wrote recAlgdep functions which apply LLL to find reciprocal pols*/
    
    Kp   := Parent(a);
    p    := Prime(Kp);
    m    := Precision(Parent(a));
    RKp<z> := PolynomialRing(Kp);
    
    ZZ := Integers();
    QQ := Rationals();
   
    PolZ<x> := PolynomialRing(ZZ);
    PolQ<x> := PolynomialRing(QQ);
    zeta := Roots(RKp!CyclotomicPolynomial(p^2-1))[1][1];
    for m := 0 to 10 do
	for k in [0..p-1] do
	    P1 := recAlgdep(a*zeta^k*p^m,deg);
	    PQ := Evaluate(PolQ!P1,p^(-m)*x);
	    LT := Coefficient(P1,deg);
	    if LT/p^Valuation(LT,p) eq 1 then
		print " found p-reciprocal polynomial!";
		print "(p^2-1)-th root of unity: zeta^", k; 
		return PQ;
	    end if;
	end for;
    end for;
    print "Not recognised!";
    return 1*x^0;
end function;


function ThoroughAlgdep2(a,deg)
    Kp   := Parent(a);
    p    := Prime(Kp);
    m    := Precision(Parent(a));
    RKp<z> := PolynomialRing(Kp);
    zeta := Roots(RKp!CyclotomicPolynomial(p^2-1))[1][1];
    
    ZZ := Integers();
    QQ := Rationals();
   
    PolZ<x> := PolynomialRing(ZZ);
    PolQ<x> := PolynomialRing(QQ);
    
    P := PolZ!x^deg;
    for k := 0 to ZZ!((p^2-1)/2) do
	P1 := algdep(a*zeta^k,deg);
	LT := Coefficient(P1,deg);
	if LT/p^Valuation(LT,p) eq 1 then
	    for m := 0 to 10 do
		PQ := Evaluate(PolQ!P1,p^m*x);
		if IsReciprocal(PQ) and Degree(PQ) le Degree(P) then
		    P := Evaluate(PQ,p^(-m)*x);
		end if;
	    end for;
	end if;
    end for;
    if not P eq x^deg then 
	print " found p-reciprocal polynomial!";
	return P;
    end if;
    print "Not recognised!";
    return 1*x^0;    
end function;
