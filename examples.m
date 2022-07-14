/* example D=77, p=3, h+ =2 from thesis:*/
/* load "main.m"; */
/* P := GSUnit(D77F2,3, 50 : GSAd := false); */
function example_computation(Q,p,m)
    /* Q is a quadratic form with squarefree discriminant */
    /* p is a prime inert in F */
    /* m is a precision parameter */
    /* Q := D77F1; */
    D := Discriminant(Q);
    F := QuadraticField(D);
    O := MaximalOrder(F);
    clno := #ReducedOrbits(QuadraticForms(D));

    PolQ<x> := PolynomialRing(QQ);
    assert KroneckerSymbol(D,p) eq -1; /* p inert */
    G := Diagonal_Restriction_Derivative(Q,p,m);
    beta := Exp(Coefficient(G,0));


    pval := -ZZ!(Meyer2(Q)*GenusFieldRootsOf1(D));
    print "pval equals", pval;

    /* f := algdep(beta*p^-pval,clno); */
    f := GSAlgdep(beta,clno,pval);    

    /* f := Evaluate(PolQ!f,3*x)/3; */
    print "min poly = ", f;
    print "with discriminant", Discriminant(f);
    H := AbsoluteField(ext<F | f>);
    /* H := ext<F | f>; */
    /* assert D^2 eq Discriminant(MaximalOrder(H)); */

    eps := Roots(f,H)[1][1];
    print "epsilon = ", eps;
    /* Fp := UnramifiedExtension(pAdicRing(3,50),2); */
    Fp, phi := Completion(F,p*O);
    H := AbsoluteField(H);
    Hp, psi := Completion(H,Factorisation(p*MaximalOrder(H))[1][1] : Precision := Precision(Parent(beta)));
    print "approximate unit in Fp equals", beta;
    print "Image of root in completion equals", psi(eps);

    print "Image of eps + 1/eps = ", psi(eps) + 1/psi(eps);
    print "Image of 3*(beta + 1/beta) = ", 3*(beta + 1/beta);

    print "---------------------";
    RFp := PolynomialRing(Fp);
    zeta := Roots(RFp!CyclotomicPolynomial(p^2-1))[1][1];
    beta := Fp!beta;


    print "beta lives in ", Parent(beta);
    print "psi(eps) lives in ", Parent(psi(eps));

    /* for l in [0..(p^2-2)] do */
    /* 	print "Image of beta*zeta^l + 1/zeta*beta^l for l = ", l," equals", beta*zeta^l + 1/(beta*zeta^l); */
    /* end for; */
    /* Coefficients(psi(eps)); */
    return 0;
end function;

/* function temp() */
/*     K := QuadraticField(321); */
/*     R<x> := PolynomialRing(QQ); */
/*     f := 16807*x^6 - 88200*x^5 + 204624*x^4 - 266219*x^3 + 204624*x^2 - 88200*x + 16807; */
/*     H<u> := ext<K | f>; */
/*     zeta := Roots(x^2-x+1,H)[1][1]; */

/*     for i := 0 to 5 do */
/* 	g := MinimalPolynomial(u*zeta^i); */
/* 	print i, GaloisGroup(ext<K | Evaluate(R!g,x^3)>), "\n"; */
/* 	if IsHCF(g,321) then */
/* 	    print "the polynomial", g, "generates the HCF of Q(sqrt(321))"; */
/* 	end if; */
/*     end for; */
/*     return 0; */
/* end function; */

function IsHCF(P,D)
    /* Test if the extension of F = Q(sqrt(D)) is the Hilbert class field */
    PolZ := PolynomialRing(ZZ);
    print "testing P = ", P;
    h := #ReducedOrbits(QuadraticForms(D));
    F := QuadraticField(D);
    if Degree(PolZ!P) le 1 then
	return false;
    end if;
    Fac1 := Factorisation(P);
    P := Fac1[#Fac1][1];
    H := ext<F | P>;
    Delta := Discriminant(MaximalOrder(AbsoluteField(H)));
    /* Factorisation(Delta); */
    /* test if D and Delta share prime factors: */
    delta_factors := {f[1] : f in Factorisation(Delta)};
    delta_mults := {f[2] : f in Factorisation(Delta)};
    D_factors := {f[1] : f in Factorisation(D)};
    D_mults := {f[2] : f in Factorisation(D)};
    print "delta factors:", delta_factors;
    print "D factors:", D_factors;
    disc_ok := (delta_factors eq D_factors) and #delta_mults eq #D_mults;

    if delta_factors eq (D_factors join {ZZ!2}) then
	print "Found poln up to factors of 2", P;
    end if;
    
       
    /* for tuple in Factorisation(Delta) do */
    /* 	ell := tuple[1]; */
    /* 	if D mod ell  */
    return disc_ok and IsAbelian(H) and (Degree(H) eq h);

end function;



function batch_compute_D(disc_bd, p : m := 50, disc_start := 0)
    Filename := "data/D" * IntegerToString(disc_bd) * "p" *IntegerToString(p) * "prec" * IntegerToString(m) *".txt";
    if disc_start eq 0 then
	/* if not specified, start new file */
	Write(Filename, "D,p, Pol" : Overwrite := true);
	disc_start := 5;
    else
	/* but if we're "resuming computations" then we don't */
	Write(Filename, "D,p, Pol" : Overwrite := false);
    end if;
    for D in [disc_start..disc_bd] do
	/*if D fund disc and  p inert in Q(sqrt(D)) */
	found_flag := false;
	SqF_disc := {f[2] mod 2 : f in Factorisation(D)} eq {1};
	if IsFundamentalDiscriminant(D) and SqF_disc  and KroneckerSymbol(D,p) eq -1 then
	    Orbs := Reverse(ReducedOrbits(QuadraticForms(D)));
	    if #Orbs gt 1 then
		for Q in Orbs do
		    try
			P := GSUnit(Q[1],p,m); /* if this fails, print message and continue */
		    catch e
			print "could not find GS unit for discriminant", D;
		    end try;
		    if IsHCF(P,D) then
			found_flag := true;
			String := Sprint(D)* ", "* Sprint(p) *", "*Sprint(P);
			Write(Filename, String);
			break;

		    end if;
		end for;
		if not found_flag then
		    /* /\* try with more precision *\/ */
		    /* print "TRYING AGAIN W 3 TIMES PRECISION"; */
		    /* for Q in Orbs do  */
		    /* 	try */
		    /* 	    P := GSUnit(Q[1],p,3*m); /\* if this fails, print message and continue *\/ */
		    /* 	catch e */
		    /* 	    print "could not find GS unit for discriminant", D; */
		    /* 	    break; */
		    /* 	end try; */
		    /* 	if IsHCF(P,D) then */
		    /* 	    found_flag := true; */
		    /* 	    String := Sprint(D)* ", "* Sprint(p) *", "*Sprint(P); */
		    /* 	    Write(Filename, String); */
		    /* 	    break; */
		    /* 	end if; */
		    /* end for; */
		print "could not find GS unit for discriminant", D;
		String := Sprint(D)* ", "* Sprint(p) *", 0";
		Write(Filename, String);
		end if;
	    end if;
	end if ;
    end for;
    return 0;

end function;
    
function batch_compute_p(prime_bd, D : m:=50)
    /* initiate file etc */
    Filename := "data/p" * IntegerToString(prime_bd) * "D" *IntegerToString(D) * "prec" * IntegerToString(m) *".txt";
    Write(Filename, "D,p, Pol" : Overwrite := true);

    /* certain sanity checks */
    Orbs := Reverse(ReducedOrbits(QuadraticForms(D)));
    assert #Orbs gt 1;
    assert {f[2] mod 2 : f in Factorisation(D)} eq {1}; /* make sure discriminant is squarefree */
    assert IsFundamentalDiscriminant(D);


    /* Compute arithmetic data including valuation vector of min polys */
    h := #ReducedOrbits(QuadraticForms(Discriminant(F)));
    e := GenusFieldRootsOf1(D);
    Lvals := [];
    for Q in ReducedOrbits(QuadraticForms(D)) do
	Qf := Q[1];
	print Qf, "has Meyer special value equal to ", Meyer2(Qf);
	ord := ZZ!(Meyer2(Qf)*e);
	Append(~Lvals,ord);
    end for;
    LGCD := GCD(Lvals);
    for l in [1..#Lvals] do
	Lvals[l] := Lvals[l]/LGCD;
    end for;
    
    /* Compute quadratic forms data; indep of p */
    Fs_list := [**];
    Forms_list := [**];
    for l in [1..h] do	     
	Fs, Forms := Diagonal_Restriction_data(Orbs[l][1],m);
	Append(~Fs_list,Fs);
	Append(~Forms_list,Forms);
    end for;

    /* main loop */
    for p in [3..prime_bd] do
	if IsPrime(p) and KroneckerSymbol(D,p) eq -1 then
	    found_flag := false;
	    for i in [1..h] do
		try
		    drd := diagonal_restriction_derivative(Orbs[i][1],p,m,Fs_list[i],Forms_list[i] : pprec := pprec);
		    a := Exp(Coefficient(drd,0));
		    P := GSAlgdep(a*QQ!(p^(ZZ!(Lvals[i]))), h,Lvals); 
		catch e
		    print "could not find GS unit for discriminant", D;
		    break;
		end try;
		
		if IsHCF(P,D) then
		    found_flag := true;
		    String := Sprint(D)* ", "* Sprint(p) *", "*Sprint(P);
		    Write(Filename, String);
		    break;
		else
		    print "could not find GS unit for prime", p;
		end if;
	    end for;
	    if not found_flag then
		print "could not find GS unit for discriminant", D;
		String := Sprint(D)* ", "* Sprint(p) *", 0";
		Write(Filename, String);
	    end if;
	end if;
    end for;
    return 0;

end function;
