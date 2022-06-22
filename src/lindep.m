function StupidCoercion(x,r)

	xc := Parent(r)!0;
	for i := 0 to Degree(Parent(x))-1 do
		xc := xc + x[i+1]*r^i;
	end for;
	
	return xc;

end function;

function lindep(List : prt := true)

    ZZ := Integers();
    QQ := Rationals();
    RR:=RealField(500);
    
    Kp := Parent(List[2]);
    p := Prime(Kp);
    m := Precision(Kp);
    N := p^(Floor(5*m/7));
    
    len := #List;
    M := ZeroMatrix(RR,len+1,len+1);
    for j:=1 to len do
        M[j,j]:=1;
        M[j,len+1]:=QQ!(List[j]);
    end for;
    M[len+1][len+1]:=N;
    Y,T:=LLL(M);
    
//     print ChangeRing(M,Integers());
//     print "";
//     print ChangeRing(Y,Integers());
//     print "";
    
	vec := [ZZ!(Y[2][len+1] - Y[2][1])];
	sum := vec[1]*List[1];
	for i := 2 to len do
		Append(~vec,ZZ!(-Y[2][i]));
		sum := sum + vec[i]*List[i];
	end for;
	
	if prt eq true then
		print "If lindep succeeded, this should be zero: ", sum; 
	end if;

    return vec, sum;
   
end function;



// This function computes the logarithms of the p-units in a number field K 
function pUnitLogs(K,p,m : j := 1)

	U, mU := SUnitGroup(p*Integers(K));
	U  := TorsionFreeSubgroup(U);
	r  := UnitRank(K);
	rp := #Generators(U);
	
	f  := MinimalPolynomial(K.1);
	Kp := UnramifiedExtension(pAdicField(p,m),2);
	//Kp := pAdicField(p,m);
	Rt := Roots(f,Kp)[j][1];
	
	Logs := [];
	for i := r+1 to rp do
		assert Valuation(Coefficient(MinimalPolynomial(K!mU(U.i)),0),p) ne 0;
		up := StupidCoercion(K!mU(U.i),Rt);
		logup := Log(Norm(up/p^Valuation(up)));
		Append(~Logs,logup);
	end for;
	
	return Logs, [U.i : i in [r+1 .. rp]], mU;

end function;



// This looks for the GS unit via lindep
function GrossStarkSearch(c,K : opt := 1)

	p := Prime(Parent(c));
	m := Precision(Parent(c));
	for j in [opt] do
	//for j := 1 to Degree(K) do
		print "Root ", j;
		Logs, U, mU := pUnitLogs(K,p,m : j := j);
		vec, sum := lindep(Append(Logs,Parent(Logs[1])!c) : prt := false);
		print "Lindep gives: ", vec;
		print "Valuation: ", Valuation(sum);
		ugl := K!1;
		for i := 1 to #Logs do
			ugl := ugl*(K!mU(U[i]))^(ZZ!(vec[i]/12));
		end for;
		f := MinimalPolynomial(ugl);
		lcm := 1;
 		for i := 0 to Degree(f) do
 			lcm := Lcm(lcm,Denominator(Coefficient(f,i)));
 		end for;
 		f := lcm*f;
  		print "Global unit satisfies: ", f;
//  		for i := 0 to Degree(f) do
//  			print "Coefficient ", i, Factorisation(ZZ!Coefficient(f,i));
//  		end for;
	end for;
	
	return "Done";

end function;
