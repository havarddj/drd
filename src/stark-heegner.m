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
    RR := RealField(500);
    
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
/* function GrossStarkSearch(c,K : opt := 1) */

/* 	p := Prime(Parent(c)); */
/* 	m := Precision(Parent(c)); */
/* 	for j in [opt] do */
/* 	//for j := 1 to Degree(K) do */
/* 		print "Root ", j; */
/* 		Logs, U, mU := pUnitLogs(K,p,m : j := j); */
/* 		vec, sum := lindep(Append(Logs,Parent(Logs[1])!c) : prt := false); */
/* 		print "Lindep gives: ", vec; */
/* 		print "Valuation: ", Valuation(sum); */
/* 		ugl := K!1; */
/* 		for i := 1 to #Logs do */
/* 			ugl := ugl*(K!mU(U[i]))^(ZZ!(vec[i])); */
/* 		end for; */
/* 		f := MinimalPolynomial(ugl); */
/* 		lcm := 1; */
/*  		for i := 0 to Degree(f) do */
/*  			lcm := Lcm(lcm,Denominator(Coefficient(f,i))); */
/*  		end for; */
/*  		f := lcm*f; */
/*   		print "Global unit satisfies: ", f; */
/* //  		for i := 0 to Degree(f) do */
/* //  			print "Coefficient ", i, Factorisation(ZZ!Coefficient(f,i)); */
/* //  		end for; */
/* 	end for; */
	
/* 	return f; */

/* end function; */



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
	
	Fp   := pAdicField(p,m);
	R<q> := PowerSeriesRing(Fp,m);
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


function DiagResDerivOP(F,p,m,prec)
    /* Compute the ordinary projection of the diagonal restriction derivative */
    nterms  := DimensionClassicalSpace(2+EisWeight(p)*Floor(prec*(p+1)/(ap(p)*p)));
    /* print "Number of q-expansion coefficients to be computed: ", nterms; */
    /* print ""; */
    DRD := Diagonal_Restriction_Derivative(F,p,nterms : pprec := m);
    /* print "Diagonal restriction derivative:", DRD; */
    /* print "Computing ordinary projection:"; */
    OP := OrdinaryProjection(DRD);
    return OP;
end function;

intrinsic SHPoints(F,p,m : pprec := m, E:= EllCurvesData(p)[1], DoAlgdep := false, polred := false) -> Any
{Compute stark-heegner points}
    
    ZZ := Integers();
    QQ := Rationals();

    M := ModularForms(Gamma0(p),2);
    assert Dimension(CuspidalSubspace(M)) eq 1;

    D := Discriminant(F);
    print "Computing point on curve",E;
    print "defined over narrow Hilbert class field of Q(sqrt D) for D =", D;

    /* Compute ordinary projection */
    OrdProj := DiagResDerivOP(F,p,m,pprec+20);

    Rp<s> := Parent(Coefficient(OrdProj,0));
    Fp<sf> := FieldOfFractions(Rp);
    R<q> := PowerSeriesRing(Rp,m);
    Mp :=  BaseExtend(M,Rp);

    sqrtD := Rp!Sqrt(Rp!D);
    G := Mp!OrdProj;

    
    Combo, B := IsClassical(G);
    
    /* print "Computing GS unit:"; */
    /* ct := Coefficient(OrdProj,0); */
    /* Orbs := ReducedOrbits(QuadraticForms(D)); */
    /* h := #Orbs; */
    /* e := GenusFieldRootsOf1(D); */
    /* Lvals := []; */
    /* for orb in Orbs do */
    /* 	Q := orb[1];	 */
    /* 	ord := ZZ!(Meyer2(Q)*e); */
    /* 	Append(~Lvals,ord); */
    /* end for; */
    /* expt := (ZZ!(Meyer2(F)*e)); */
    /* print "should be small:", Coefficient(G - Combo[1]*Parent(G)!B[1],0); */

    /* eps := GSAlgdep(Exp(e*Combo[1]*(p-1)/24)*QQ!(p^expt), h, Lvals, D); */
    /* if eps ne 0 then  */
    /* 	print "GS unit satisfies (up to powers of p)", eps; */
    /* else */
    /* 	print "GS unit not found, try higher precision!"; */
    /* end if; */
    print "-------------- \n \n \n";
    print "Classical basis for M_2(Gamma0(p)) is ", B;
    print "Combo is ", Combo;
    /* return to computation of SH points  */

    Lrat :=  LRatio(ModularSymbols(E),1);
    print "Rational part of L(1,f):", Lrat;

    assert Lrat eq Fudge(E);
    
    u := Exp(Combo[2]/(Lrat));
    print "Point in Qp*/q^\Z is ", u;

    q  := Fp!qParameter(E,p,m);
    ETate := EllipticCurve([1,0,0,TateA4(q,m),TateA6(q,m)]);

    /* print "Tate curve given by:", ETate; */
    Ewei, f1, f2 := WeierstrassModel(ETate);
    /* return f1; */
    /* print "Weierstrass Model:", Ewei; */

    assert Valuation(q) gt 1;
    // Value of the uniformisation parameter, test whether it is in q^Z.
    triv := false;
    for i := -m to m do
	if Valuation(u-q^i) ge m then 
	    print "u: ", u, " q^i:", q^i;
	    triv := true; // u maps to the origin of E.
	end if;
    end for;
    print "-------------------- \n\n";
    // Tate parametrisation for u.
    if triv eq false then 
	X := TateX(u,q);
	Y := TateY(u,q);
	print "X = ", X;
	print "Y = ", Y;
	
	Z := Parent(q)!1;
	print "Should be zero if point is on the Tate curve: ", Y^2 + X*Y - X^3 - TateA4(q,m)*X - TateA6(q,m);
	/* assert Valuation(Y^2 + X*Y - X^3 - TateA4(q,m)*X - TateA6(q,m)) ge m-1; */
    else
	X := 0;
	Y := 1;
	Z := 0;
    end if;
    Ep := ChangeRing(E, Parent(q));
    psi := Isomorphism(Ewei, Ep); /* magma says E isomorphic to Ep, but not ETate */
    P := psi(Ewei!f1(ETate![X,Y,Z]));

    print "Point on Weierstrass curve has coords", P;

    if DoAlgdep then
	h := #ReducedOrbits(QuadraticForms(D));
	X := algdep(P[1],h);
	Y := algdep(P[2],h);
	print "algdep thinks X and Y are ", X, Y;
	K := NumberField([X,Y]);
	EK := BaseChange(E,K);
	Q := EK![X,Y,1];
	return Q, [];
    end if; 

	
    /* H is the narrow Hilbert class field of Q(sqrtD) */
    H := AbsoluteField(NumberField(RayClassField(Integers(QuadraticField(D))*1,[1,2])));
    /* use Edgar Costa's Polred port to potentially speed up descent computation */
    /* Requires having the spec attached. */
    /* if polred then		 */
    /* 	H := NumberField(Polred(H)); */
    /* end if; */
    
    EH := BaseChange(E,H);
    
    print "Computing Mordell-Weil group over narrow Hilbert class field";
    if Degree(H) gt 4 then
	print "since [H:Q] =",Degree(H), "run SetClassGroupBounds(\"GRH\");";
	print "to make computation manageable";
    end if;
    G, Psi := MordellWeilGroup(EH);
    print G;
    print "Generators are:";
    FreeGens := [];
    for g in Generators(G) do
	print Psi(g), "of order:", Order(g);
	if Order(g) eq 0 then
	    Append(~FreeGens,Psi(g));
	end if;
    end for;

    log := FormalLog(E : Precision := 50);
    LogList := [];
    for Q0 in FreeGens do
	Q := (p-1)*Q0;
	MinPoly := MinimalPolynomial(-Q[1]/Q[2]);
	z := Roots(MinPoly,Fp)[1][1];
	Append(~LogList, Evaluate(log,z));
    end for;
    Append(~LogList, (p-1)*Evaluate(log,-P[1]/P[2]));
    print "List of formal group elements: ", LogList;
    
    LindepVec := lindepQp2(LogList);
    print "lindep returns", LindepVec;

    if [Abs(LindepVec[i]) lt 100 : i in [1..#LindepVec]] ne
       [true :i in [1..#LindepVec]] then
	print "lindep most likely found garbage";
	return E!0, [];
    end if;
    Q := &+[FreeGens[i]*LindepVec[i]/LindepVec[#FreeGens+1] : i in [1..#FreeGens]];
    print "Stark-Heegner point might be", Q;
    /* output Q and anything  */
    Ldash := [LindepVec[i]/LindepVec[#FreeGens+1] : i in [1..#FreeGens]];
    /* test stuff: */

    print "lambda_f = ", Combo[2];
    Qdash := (p-1)*Q;
    MinPoly := MinimalPolynomial(-Qdash[1]/Qdash[2]);
    z := Roots(MinPoly,Fp)[1][1];
    print "-L_rat * log_E (P) = ", -Lrat*Evaluate(log,z)/(p-1);
    print "difference:", -Combo[2] - (Lrat*Evaluate(log,z)/(p-1));
    return Q, Ldash;
end intrinsic;
