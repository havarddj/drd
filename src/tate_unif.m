function Fudge(E)
	
	Sha := Floor(ConjecturalRegulator(E)); 	
	Tam := 1;
	for no in TamagawaNumbers(E) do
		Tam := Tam*no;
	end for;
	fudge := Sha*Tam/Order(TorsionSubgroup(E))^2;
	
	r,Lr1 := AnalyticRank(E: Precision:=50);
	OmE   := RealPeriod(E);
	// print "Fudge factor: ", fudge, Lr1/OmE; // Check that this agrees with analytic calculation.
	
	return fudge;

end function;

function qParameter(E,p,m)

	jE   := jInvariant(E);
	vjE  := Valuation(jE,p);
	assert vjE lt 0; // E must be a Tate curve!
	
	Qp   := pAdicField(p,m);
	R<q> := PowerSeriesRing(Qp,m);
	Jq   := jInvariant(q);
	g    := Reverse(1/Jq);
	
	return Evaluate(g,1/jE);

end function;


// This function computes the sum sk(q), see Silverman p.423
function TateSk(q,k,m)

	Sk := q/(1-q);
	qi := q;
	for i := 2 to m-1 do
		qi := qi*q;
		Sk := Sk + i^k*qi/(1-qi);
	end for;
	
	return Sk;
	
end function;

// This function computes the coefficient a4(q), see Silverman p.423
function TateA4(q,m)

	return -5*TateSk(q,3,m);
	
end function;

// This function computes the coefficient a4(q), see Silverman p.423
function TateA6(q,m)

	ZZ := Integers();
	A6 := 0;
	qi := 1;
	for i := 1 to m-1 do
		qi := qi*q; 
		A6 := A6 + -ZZ!((5*i^3+7*i^5)/12)*qi/(1-qi);
	end for;
	
	return A6;
	
end function;

// This function returns the X-coordinate of the point u in Cp*/q^Z, up to precision m.
function TateX(u,q)

	m := Precision(Parent(u));
	X := u/(1-u)^2;
	qi := 1;
	for i := 1 to m-1 do
		qi := qi*q;
		X := X + qi*u/(1-qi*u)^2 + qi*u/(u-qi)^2 - 2*qi/(1-qi)^2;
	end for;
	
	return X;

end function;

// This function returns the Y-coordinate of the point u in Cp*/q^Z, up to precision m.
function TateY(u,q)

	m := Precision(Parent(u));
	Y := u^2/(1-u)^3;
	qi := 1;
	for i := 1 to m-1 do
		qi := qi*q;
		Y := Y + (qi*u)^2/(1-qi*u)^3 - qi*u^2/(u-qi)^3 + qi/(1-qi)^2;
	end for;
	
	return Y;

end function;

function EllCurvesData(p)
    /* Return representatives for all isogeny classes of
       elliptic curves of conductor p   */
    D := CremonaDatabase();
    AllEs := EllipticCurves(D,p);
    IsogNum := NumberOfIsogenyClasses(D,p);
    Es := [*AllEs[1]*];
    for E0 in AllEs do
	if [IsIsogenous(E0,E) : E in Es] eq [false : E in Es] then
	    Append(~Es,E0);
	end if;
    end for;
    return Es;
   	      
end function;
