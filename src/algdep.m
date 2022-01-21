function algdepZpm(a,deg)

	N  := Modulus(Parent(a));
	ZZ := Integers();
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

    ZZ := Integers();
    QQ := Rationals();
    RR := RealField(500);
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

    ZZ := Integers();
    QQ := Rationals();
    RR := RealField(500);
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
    /* Important! Input CT, not Exp(CT) */

    /* Håvard 21/01/22: added check for reciprocality */
    Kp   := Parent(a);
    p    := Prime(Kp);
    m    := Precision(Parent(a));
   
    ZZ := Integers();
    QQ := Rationals();
   
    PolZ<x> := PolynomialRing(ZZ);
    PolQ<x> := PolynomialRing(QQ);
    
    for i := 1 to nn do
    	for j := 1 to nn do
    	    if IsDivisibleBy(j,p) eq false then
		P1 := algdep(Exp(a*i/j),deg);
		PQ := PolQ!P1;
		LT := Coefficient(P1,deg);
		if LT/p^Valuation(LT,p) eq 1 then
		    for k := -nn to nn do 
			if IsReciprocal(Evaluate(PQ,p^k*x)) then
			    print " found p-reciprocal polynomial!";
			    print "i,j = ", i,j;    
			    return P1;
			end if;
		    end for;
		end if;
	    end if;
	end for;
    end for;
    print "Not recognised!";
    return 1*x^0;
end function;
