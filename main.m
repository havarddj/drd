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
    print "";
    DRD := Diagonal_Restriction_Derivative(F,p,nterms : pprec := m);
    print "Diagonal restriction derivative:", DRD;
    print "";	      
    print "Computing Gross-Stark unit";
    ClNo := #ReducedOrbits(QuadraticForms(Discriminant(F)));
    GSAlgdep(Exp(Coefficient(DRD,0)),ClNo, Meyer(F));

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
    /* print "X-coordinate satisfies : ", algdep(Point[1],#RedF); */
    /* print "Y-coordinate satisfies : ", algdep(Point[2],#RedF); */

    /* return Point; */
    /* The following is taken from "Overconvergentlatest.m", copied from Jan's website*/
    D  := Discriminant(F);
    D1 := 0;
    D2 := 0;
    for d1 in Divisors(D) do
	d2 := ZZ!(D/d1);
	if KroneckerSymbol(-d1,p) eq -1 and IsDiscriminant(-d1) and KroneckerSymbol(-d2,p) eq 1 and IsDiscriminant(-d2) then
	    D1 := -d1;
	    D2 := -d2;
	end if;
    end for;
    K := QuadraticField(D2);
    Ei := ChangeRing(E,K);
    Gens := Generators(Ei);
    i := 1;
    gen := Gens[i];
    while Order(gen) gt 0 do
	i := i + 1;
	gen := Gens[i];
    end while;
    
    // Local definitions.
    Pointp := Ep!f1(ETate![X,Y,Z]);
    E_tens := ChangeRing(E,Parent(q));
    psi    := Isomorphism(Ep,E_tens);
    Point  := psi(Pointp);
    genp1  := (p-1)*gen;
    
    // Compute formal logarithm.
    log  := FormalLog(E : Precision := 50);
    log1 := Evaluate(log,-Point[1]/Point[2]);
    print log1;
    fgen := MinimalPolynomial(genp1[1]/genp1[2]);
    root := Roots(fgen, Parent(u))[1][1];
    log2 := Evaluate(log,-root);
    fff := algdep((p-1)*log1/log2,1);
    print "Dependence between points: ", fff;
    print "";
    print "Stark-Heegner point: ";
    print Roots(fff,Rationals())[1][1]*Fudge(E), " \\log_{", p, "} \\left(", gen[1], ",", gen[2] ," \\right) ";
    print "";
    print " lies on curve", E;
    print "";
    print "K equals Q adjoined sqrt", D2;
    return Point, log1;
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
    /* Combo := Eltseq(G); */
    /* print "Spectral expansion coefficients:", Combo; */
    /* print "IsClassical gives", IsClassical(OrdProj); */
    Combo, B := IsClassical(G);

    E := EllipticCurve(IntegerToString(p) cat "a");
    return DarmonDetect(E,Exp(Combo[2]/Fudge(E)),F,p,m);
    /* Next compute numbers lambda_f' from spectral expansion  */
    /* ND := NewformDecomposition(ModularSymbols(Cp)); */
    /* Lalgs := [LRatio(g,1) : g in ND]; */
    /* print "L_algs: ", Lalgs; */
    
    /* lambdafs := [**]; */
    /* for n in [1..#Lalgs] do */
    /* 	if not Lalgs[n] eq 0 then */
    /* 	    Append(~lambdafs,-Combo[n]/(4*Lalgs[n])); */
    /* 	else  */
    /* 	    Append(~lambdafs,0); */
    /* 	end if; */
    /* end for; */
    /* print "lambdafs:", lambdafs; */

    /* Es := EllCurvesData(p); */
    /* /\* Now we want to detect which elliptic curves correspond to which */
    /* eigenforms *\/ */
    /* lfsOrdered := [**]; */

    /* for E in Es do */
    /* 	Ecombo := Eltseq(Cp!Eigenform(E,m)); */
    /* 	print "Ecombo of ", E, "equals", Ecombo; */
    /* 	i := 1; */
    /* 	while Ecombo[i] eq 0 do */
    /* 	    i := i+1; */
    /* 	end while; */
    /* 	Append(~lfsOrdered,lambdafs[i]); */
    /* end for; */
    /* print "lfsOrdered = ", lfsOrdered; */

    /* return [DarmonDetect(Es[i],Exp(Rp!lambdafs[i]),F,p,m) : i in [1..#Es]]; */
end function;



function GSUnit(F,p,m : verbose:=true, GSAd:=true)
    D := Discriminant(F);
    assert KroneckerSymbol(D,p) eq -1; /* p inert */
    if verbose then
	print "Computing diagonal restriction derivative";
    end if;
    /* DRD := Diagonal_Restriction_Derivative(F,p,m : pprec := 400); */
    DRD := Diagonal_Restriction_Derivative(F,p,m);
    ct := Coefficient(DRD,0);

    ClNo := #ReducedOrbits(QuadraticForms(Discriminant(F)));
    if verbose then
	print "";
	print "Running thorough algdep on exp(ct)";
	print "";
    end if;    

    /* return ThoroughAlgdep(Exp(ct),ClNo : pval := Meyer(F)); */

<<<<<<< HEAD

    /* To compute the valuation of the constant term, our choice of
    normalisation is precisely so that the constant term is p^R where
    R is the sum of the positive slopes of the vector of L-values */
    e := GenusFieldRootsOf1(D);
    Lvals := [];
    for Q in ReducedOrbits(QuadraticForms(D)) do
	Qf := Q[1];
	print Qf, "has Meyer special value equal to ", Meyer2(Qf);
	ord := ZZ!(Meyer2(Qf)*e);
	Append(~Lvals,ord);
>>>>>>> 75c667466d73e41785316bbba97d25440454a307
    end for;

    /* print(pord); */
    if GSAd then
<<<<<<< HEAD
	expt := (ZZ!(Meyer2(F)*e));
	print "exponent of p", expt;
	return GSAlgdep(Exp(ct)*QQ!(p^expt), ClNo, Lvals);
    else
	/* return algdep(Exp(ct),2*ClNo); */
	return ThoroughAlgdep(Exp(ct)*QQ!(p^(ZZ!(Meyer2(F)*2))),ClNo : nn:=30);
=======
>>>>>>> 75c667466d73e41785316bbba97d25440454a307
    end if;
end function;
/* function HeckeEulerFactor(chi,p) */
/*     /\* Return Euler factor above p of Hecke L-function of chi *\/ */
/*     K := NumberField(FieldOfFractions(Ring(Domain(chi)))); */
/*     /\* Decomposition(K,p) returns *\/ */
/*     return *&[] */
	

function HeckeLFunction(chi)
    /* We roll our own Hecke L-function because magma only works
       for primitive L-functions */
    K := NumberField(FieldOfFractions(Ring(Domain(chi))));
    O := Integers(K);
    /* finpart, infpart := Modulus(chi); /\* extract signature for gamma-factor *\/ */
    /* gamma := [n - 1 : n in infpart]; */
    gamma := [1,1]; 		/* not sure but this seems right */
    cond := Abs(Discriminant(K))*Norm(Conductor(chi));
    
    R<x> := PolynomialRing(CyclotomicField(#Parent(chi)));
    /* We determine local factors by L(s) = prod_p (Lp(p^-s)) */
    cf := func<p,d | &*[1-chi(I[1])*x^Degree(I[1]) : I in Factorisation(p*O)]>;
    /* Can also use EulerFactor(chi,p) */
    /* if chi is trivial, then we get the dedekind zeta fn */
    /* Copied from https://www.math.uzh.ch/sepp/magma-2.17_10-cr/html/text1391.htm */
    if chi eq Parent(chi).0 then	
	h := #ClassGroup(O);
	reg := Regulator(K);
	mu := #TorsionSubgroup(UnitGroup(O));
	r1,r2 := Signature(K);
	return LSeries(1, gamma, cond, cf:
		       Parent:=K, Sign:=1, Poles:=[1],
		       Residues := [-2^(r1+r2)*Pi(RealField())^(r2/2)*reg*h/mu]);
    else
	return LSeries(1, gamma, cond, cf:
		       Parent:=K, Sign:=RootNumber(chi));
    end if;
    /*  */
    /* Note: run CheckFunctionalEquation(L); to make sure this works!! */
    /* There's a subtlety with conductors:
       even though chi^2 for K = Q(sqrt(321)), chi generator, has trivial modulus,
   the associated primitive character lives on the wide class group! So in magma, the
   conductor is not just an integral ideal, but a modulus.
   Compare >Modulus(chi^2); Conductor(chi^2);*/
   /* In fact, the Gamma-factors imply that chi^2 doesn't have "nice" L-function,
    */
end function;

function PartialLValue(A,s)
    /* Compute partial L-value L(s,A) analytically by using the fact that
     characters on Cl+ form an orthogonal basis for the space of functions,
     and built-in Hecke character functionality.
     Here A is a class in Cl+ represented by a QUADRATIC FORM,
     and s is any real number. 
     TODO: use ring class characters when D is not square-free */
    D := Discriminant(Parent(A));
    K := QuadraticField(D);
    Astar := AntiguousForm(A);

    a := Ideal(A);
    /* astar := Ideal(Astar); */
    
    Ghat := HeckeCharacterGroup(1*Integers(K),[1,2]);
    /* print "Ghat equals", Elements(Ghat); */
    LVal := 0;
    for chi in Elements(Ghat) do
	/* if not IsPrimitive(chi) then */
	/*     print "Non-primitive chi:", chi; */
	/*     print "Primitive version:", AssociatedPrimitiveCharacter(chi); */
	/* end if; */
	/* if chi eq Ghat.0 then */
	L := LSeries(AssociatedPrimitiveCharacter(chi));
	/* else */
	/*     L  := LSeries(chi); */
	/* end if; */
	try
	    LVal := LVal + Conjugate(chi)(a)*Evaluate(L,s);
	catch e
	    if s eq 1 then
		return "Pole at s=1";
	    end if;
	end try;
    end for;
    return LVal/#Ghat;
end function;

    
function GSUnitData(D, forms, p: e:=1, prec:=75)
    assert D ge 0;
    K := QuadraticField(D);
    G := NarrowClassGroup(K);
    print "CL+ = ", G;

    H := AbsoluteField(NumberField(RayClassField(1*Integers(QuadraticField(D)),[1,2])));
    U := UnitGroup(H);
    e := #TorsionUnitGroup(H);
    print "\n - - - - - - - - - - - - - - - \n";
    print "Unit group of narrow class field = ", U;

    print "\n - - - - - - - - - - - - - - - \n";
    /* print "forms equal:", forms; */
    print "Partial L-values using Meyer's formula = ", [e*x : x in LValVec(D : forms := forms)];

    /* Now compute Lvals analytically */
    
    /* LValAnal := []; */
    /* for A in ReducedOrbits(QuadraticForms(D)) do */
    /* 	Append(~LValAnal, PartialLValue(A[1],0)); */
    /* end for; */

    /* print "\n - - - - - - - - - - - - - - - \n"; */
    /* print "Partial L-values computed analytically (magma) = ", LValAnal; */
    print "\n - - - - - - - - - - - - - - - \n";
    print "Attempting to find Gross-Stark units:";

    unit_list := [];
    for F in forms do
	Fm := QuadraticForms(D)!F;
	ct := Coefficient(Diagonal_Restriction_Derivative(Fm,p,prec),0);
	P := algdep(ct,#forms);
	print "\n For the form", Fm, "found poln", P;

	print "\n Roots of poln reduced mod p^2 are:", roots_mod_p2(P,D,p);
    end for;

    
    
    print "\n - - - - - - - - - - - - - - - \n";
    print "Partial L-values computed analytically (pari) = ";
    
    return e;
end function;

<<<<<<< HEAD
=======
>>>>>>> 75c667466d73e41785316bbba97d25440454a307
