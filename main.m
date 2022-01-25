load "./src/algdep.m";
load "./src/lindep.m";
load "./src/discs.m";
load "./src/tate_unif.m";
load "./src/overconvergent.m";
load "./src/diagres.m";

function DiagResDerivOP(F,p,m,prec)
    /* Compute the ordinary projection of the diagonal restriction derivative */
    nterms  := DimensionClassicalSpace(2+EisWeight(p)*Floor(prec*(p+1)/(ap(p)*p)));
    print "Number of q-expansion coefficients to be computed: ", nterms;
    DRD := Diagonal_Restriction_Derivative(F,p,nterms : pprec := m);
    print "Computing Gross-Stark unit";
    ClNo := #ReducedOrbits(QuadraticForms(Discriminant(F)));
    ThoroughAlgdep(Coefficient(DRD,0),2*ClNo : nn := 20);

    print "";
    print "Computing ordinary projection:";
    OP := OrdinaryProjection(DRD);
    return OP;
end function;

function DarmonDetect(E,u,F,p,m)
    Rp := Parent(u);
    Fp := FieldOfFractions(Rp);
    q  := Fp!qParameter(E,p,m);
    ETate    := EllipticCurve([1,0,0,TateA4(q,m),TateA6(q,m)]);
    Ep,f1,f2 := WeierstrassModel(ETate);
    print "u = ", u;
    print "q = ", q;
    // Value of the cocycle, test whether it is in q^Z.
    triv := false;
    for i := -m to m do
	if Valuation(u-q^i) ge m then 
	    print "u: ", u, " q^i:", q^i;
	    triv := true; // u maps to the origin of E.
	end if;
    end for;
    
    // Tate parametrisation for u.
    if triv eq false then 
	X := TateX(u,q);
	Y := TateY(u,q);
	Z := Parent(q)!1;
	print "Should be zero if point is on the Tate curve: ", Y^2 + X*Y - X^3 - TateA4(q,m)*X - TateA6(q,m);
	/* assert Valuation(Y^2 + X*Y - X^3 - TateA4(q,m)*X - TateA6(q,m)) ge m-1; */
    else
	X := 0;
	Y := 1;
	Z := 0;
    end if;

    Pointp := Ep!f1(ETate![X,Y,Z]);
    print "Pointp is: ", Pointp;
    psi    := Isomorphism(Ep,ChangeRing(E,Parent(q)));
    Point  := psi(Pointp);
    print "parent of Points", Parent(Point[1]);
    DF := Discriminant(F);
    RedF := ReducedOrbits(QuadraticForms(DF));
    print "X-coordinate satisfies : ", algdep(Point[1],2*#RedF);
    print "Y-coordinate satisfies : ", algdep(Point[2],2*#RedF);
    return Point;
end function;

function Darmonpts(F,p,m : pprec := m)

    /* Compute ordinary projection */
    OrdProj := DiagResDerivOP(F,p,m,pprec);
    Rp<s>  := Parent(Coefficient(OrdProj,0));
    Fp<sf> := FieldOfFractions(Rp);
    R<q>   := PowerSeriesRing(Rp,m);


    D := Discriminant(F);
    sqrtD := Rp!Sqrt(Rp!D);
    M := ModularForms(Gamma0(p),2);
    C := CuspidalSubspace(M);

    Mp :=  BaseExtend(M,Rp);
    Eisp := EisensteinSubspace(Mp).1;
    Cp := CuspidalSubspace(Mp);
    G := Mp!OrdProj;


    /* nterms  := DimensionClassicalSpace(2+EisWeight(p)*Floor(prec*(p+1)/(ap(p)*p))); */


    /* return OP; */

    print "ordinary projection equals", G;
    print "";
    
    /* Compute spectral expansion of G */
    Combo := Eltseq(G);
    print "Spectral expansion coefficients:", Combo;


    /* Next compute numbers lambda_f' from spectral expansion  */
    ND := NewformDecomposition(ModularSymbols(Cp));
    Lalgs := [LRatio(g,1) : g in ND];
    print "L_algs: ", Lalgs;
    
    lambdafs := [**];
    for n in [1..#Lalgs] do
	if not Lalgs[n] eq 0 then
	    Append(~lambdafs,-Combo[n]/(4*Lalgs[n]));
	else 
	    Append(~lambdafs,0);
	end if;
    end for;
    print "lambdafs:", lambdafs;

    Es := EllCurvesData(p);
    /* Now we want to detect which elliptic curves correspond to which
    eigenforms */
    lfsOrdered := [**];

    for E in Es do
	Ecombo := Eltseq(Cp!Eigenform(E,m));
	print "Ecombo of ", E, "equals", Ecombo;
	i := 1;
	while Ecombo[i] eq 0 do
	    i := i+1;
	end while;
	Append(~lfsOrdered,lambdafs[i]);
    end for;
    print "lfsOrdered = ", lfsOrdered;
    return [DarmonDetect(Es[i],Exp(Rp!lambdafs[i]),F,p,m) : i in [1..#Es]];
end function;



function GS_unit(F,p,m : verbose:=true)
    if verbose then
	print "Computing diagonal restriction derivative";
    end if;
    DRD := Diagonal_Restriction_Derivative(F,p,m : pprec := 400);
    ct := Coefficient(DRD,0);

    ClNo := #ReducedOrbits(QuadraticForms(Discriminant(F)));
    if verbose then
	print "";
	print "Running thorough algdep on exp(ct)";
	print "";
    end if;    
    /* return ThoroughAlgdep(ct,2*ClNo : nn:=30); */
    return ThoroughAlgdep2(Exp(ct),2*ClNo : nn := 20);
    /* return algdep(Exp(ct),2*ClNo); */
end function;
