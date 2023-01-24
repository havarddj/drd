
QQ := Rationals();
ZZ := Integers();
import "./src/diagres.m" : diagonal_restriction_derivative;

function overwriteLine(fileName, Str, newStr)
    /* Replace in file Filename the first line containing string str
    with string newStr, otherwise append at end
   */
    fileStr := Read(fileName);
    lineStart := Position(fileStr, Str);
    if lineStart eq 0 then
	Write(fileName, newStr);
	return "appended line";
    end if;
    preStr := Substring(fileStr, 1, lineStart-1);
    postStr := Substring(fileStr,lineStart, #fileStr - lineStart);
    lineStop := Position(postStr,"\n");
    if lineStop eq 0 then
	print("hit end of file");
	Write(fileName, preStr * newStr: Overwrite := true);
    else 
	postStr := Substring(postStr,lineStop, #postStr - lineStop+1);
	
	Write(fileName, preStr * newStr* postStr: Overwrite := true);
    end if;
    return "rewrote line";
end function;

function IsGSDisc(D,p)
    flag := true;
    /* flag := flag and IsSquarefree(D); */
    flag := flag and IsFundamentalDiscriminant(D);
    flag := flag and KroneckerSymbol(D,p) eq -1;
    flag := flag and Norm(FundamentalUnit(QuadraticField(D))) eq 1;
    flag := flag and #ReducedOrbits(QuadraticForms(D)) gt 1;
    return flag;
end function;

function batch_compute_D(disc_bd, p : m := 50, pprec := m, disc_start := 5, overwrite := false)
    PolQ<x> := PolynomialRing(QQ);
    
    Filename := "data/D" * IntegerToString(disc_bd) * "p" *IntegerToString(p) *".csv";
    
    try
	tmp := Read(Filename);
	tmp := 0;
    catch err	
	/* if not specified, start new file */
	Write(Filename, "D,p, Pol");
    end try;

    for D in [disc_start..disc_bd] do
	/*if D fund disc and  p inert in Q(sqrt(D)) */
	found_flag := false;
	computed_flag := false;
	if IsGSDisc(D,p) then
	    /* now check if we added it already */
	    if not overwrite then
		file := Read(Filename);
		pos := Position(file, Sprint(D)* ", "* Sprint(p));
		if pos gt 0 then /* pos eq 0 iff not found */
		    /* print pos; */
		    while file[pos] ne "\n" do
			if file[pos] eq "x" then
			    print "already computed for D,p =", D, ",", p;
			    computed_flag := true;
			    break;
			end if;
			pos +:= 1;
		    end while;
		end if;
	    end if;

	   if not computed_flag then
 	       Orbs := Reverse(ReducedOrbits(QuadraticForms(D)));
	       lprec := pprec;
	       LvalVec := [Abs(Meyer2(Q[1])) : Q in Orbs];
	       MinLval := Minimum(LvalVec);
			      
	       while not found_flag do
		   for Q in Orbs do
		       if #Orbs lt 4
			  or Abs(Meyer2(Q[1])) ne Maximum(LvalVec) then  /* The biggest Lvalue usually fails bc p-adic algo */
			   
        		   P := GSUnit(Q[1],p,m :  pprec:=lprec); /* if this fails, print message and continue */
			   /* now test if it generates HCF */
			   if P ne 0 then
			       found_flag := true;
			       newStr := Sprint(D)* ", "* Sprint(p) *", "*Sprint(P);
			       overwriteLine(Filename,Sprint(D)* ", "* Sprint(p),newStr);
			       break;
			   end if;
		       else
			   print "Skipped quadratic form with unit of high valuation, = ", Maximum(LvalVec);
		       end if;
			   /* now test if it generates HCF */
			   /* if P ne 0 and IsHCF(P,D) then */
			   /* 	   found_flag := true; */
			   /* 	   newStr := Sprint(D)* ", "* Sprint(p) *", "*Sprint(P); */
			   /* 	   overwriteLine(Filename,Sprint(D)* ", "* Sprint(p),newStr); */
			   /* 	   break; */
			   /* end if; */
		   end for;
		   /* if this didn't work, reset */
		   lprec +:= 20; /* bump precision if we can't find any */
		   if lprec gt 4*m then /* give up at a certain point */
		       break;
		   end if;
	       end while;
	       if not found_flag then
		   print "could not find GS unit for discriminant", D;		   
		   if Position(Read(Filename), Sprint(D)* ", "* Sprint(p)) eq 0 then
		       String := Sprint(D)* ", "* Sprint(p) *", 0";
		       Write(Filename, String);
		   end if;
	       end if;
	    end if;
	end if;
    end for;
    return 0;
		    /* if P eq 0 then */
		    /* 	a := Exp(Coefficient(Diagonal_Restriction_Derivative(Q[1],p,m),0)); */
		    /* 	if -Meyer2(Q[1])*2 in ZZ then  */
		    /* 	    P := algdep(a*p^ZZ!(-Meyer2(Q[1])*2), #Orbs); */
		    /* 	else */
		    /* 	    expt := (-Meyer2(Q[1])*6); */
		    /* 	    assert expt in ZZ; */
		    /* 	    P := algdep(a*p^ZZ!expt, #Orbs); */
		    /* 	end if; */
		    /* 	recip_flag := false; */
		    /* 	for k in [-10..10] do */
		    /* 		Pdash := Evaluate(P,p^k*x); */
		    /* 		if Coefficients(Pdash) eq Reverse(Coefficients(Pdash)) then */
		    /* 		    P := Pdash*p^-Min([Valuation(c,p) : c in Coefficients(Pdash)]); */
		    /* 		    recip_flag := true; */
		    /* 		    break; */
		    /* 		end if; */
		    /* 	end for; */
			
		    /* 	if recip_flag then */
		    /* 	    if not IsHCF(P,D) then  */
		    /* 		P := 0; */
		    /* 	    end if; */
		    /* 	else */
		    /* 	    P := 0; */
		    /* 	end if; */
		    /* end if; */
		    /* /\* sometimes it's helpful to test u^3 instead *\/ */
		    /* if P eq 0 then */
		    /* 	print "trying to algdep Exp_p(log_p(u))^3"; */
		    /* 	    P := algdep(a^3, #Orbs); */
		    /* 	    if Coefficient(P,0) lt 0 then */
		    /* 		P := -P; */
		    /* 	    end if; */
		    /* 	    cubedFlag := true; */
		    /* 	    for k in [-10..10] do */
		    /* 		Pdash := Evaluate(P,p^k*x); */
		    /* 		if Coefficients(Pdash) eq Reverse(Coefficients(Pdash)) then */
		    /* 		    P := Pdash*p^-Min([Valuation(c,p) : c in Coefficients(Pdash)]); */
		    /* 		    break; */
		    /* 		end if; */
		    /* 	    end for; */
		    /* 	    /\* not gonna test any odd boy *\/ */
		    /* 	    P := 0; */
		    /* end if; */
end function;
    
function batch_compute_p(prime_bd, D : m:=50, pprec:=m, overwrite:=false)
    PolQ<x> := PolynomialRing(QQ);
    /* certain sanity checks */
    Orbs := ReducedOrbits(QuadraticForms(D));
    h := #Orbs;
    assert h gt 1;
    /* assert IsSquarefree(D); /\* make sure discriminant is squarefree *\/ */
    assert IsFundamentalDiscriminant(D);

    Filename := "data/p" * IntegerToString(prime_bd) * "D" *IntegerToString(D) *".csv";
    
    try
	tmp := Read(Filename);
	tmp := 0;
    catch err	
	/* if not specified, start new file */
	Write(Filename, "D,p, Pol");
    end try;

    /* Compute arithmetic data including valuation vector of min polys */
    e := GenusFieldRootsOf1(D);
    Lvals := [];
    for orb in ReducedOrbits(QuadraticForms(D)) do
	Q := orb[1];
	print Q, "has Meyer special value equal to ", Meyer2(Q);
	ord := ZZ!(Meyer2(Q)*e);
	Append(~Lvals,ord);
    end for;
    LGCD := GCD(Lvals);
    for l in [1..#Lvals] do
	Lvals[l] := Lvals[l]/LGCD;
    end for;
    
    /* Compute quadratic forms data; indep of p */
    Fs_list := [**];
    Forms_list := [**];
    for i in [1..h] do	     
	Fs, Forms := Diagonal_Restriction_data(Orbs[i][1],m);
	Append(~Fs_list,Fs);
	Append(~Forms_list,Forms);
    end for;

    /* main loop */
    for p in [3..prime_bd] do
	/* cubed_flag := false; */
	computed_flag := false;
	if not overwrite then
	    file := Read(Filename);
	    pos := Position(file, Sprint(D)* ", "* Sprint(p));
	    if pos gt 0 then /* pos eq 0 iff not found */
		print pos;
		while file[pos] ne "\n" do
		    if file[pos] eq "x" then
			print "already computed for D,p =", D, ",", p;
			computed_flag := true;
			break;
		    end if;
		    pos +:= 1;
		end while;
	    end if;
	end if;
	
	if not computed_flag and IsPrime(p) and KroneckerSymbol(D,p) eq -1 then
	    cubedFlag := false;
	    found_flag := false;
	    for i in [1..h] do
		Q := Orbs[i][1];
		try
		    /* print ZZ!(+Floor(p/3)); */
		    drd := diagonal_restriction_derivative(Q,p,m,Fs_list[i],Forms_list[i]);
		    a := Exp(Coefficient(drd,0));
		    P := GSAlgdep(a*QQ!(p^Lvals[i]), h,Lvals,D);
		    
		catch e1
		    print "could not find GS unit for discriminant", D;
		    print e1;
		    break;
		end try;
		if P eq 0 then
		    print "trying to algdep Exp_p(log_p(u))^3";
		    try
			P := algdep(a^3, h);
			cubedFlag := true;
			for k in [-10..10] do
			    Pdash := Evaluate(P,p^k*x);
			    if Coefficients(Pdash) eq Reverse(Coefficients(Pdash)) then
				P := Pdash*p^-Min([Valuation(c,p) : c in Coefficients(Pdash)]);
				break;
			    end if;
			end for;
			if not IsHCF(P,D) then
			    P := 0;
			end if;
		    catch e2
			print "that didn't work either";
		    end try;
		end if;
		if P ne 0 then
		    found_flag := true;
		    newStr := Sprint(D)* ", "* Sprint(p) *", "*Sprint(P);
		    if cubedFlag then			    
			/* newStr *:= " (Rmk. char poly of u^3)"; */
			cubedFlag := false;
		    end if;
		    overwriteLine(Filename,Sprint(D)* ", "* Sprint(p),newStr);
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



function batch_compute_D_and_p(prime_bd, disc_bd : m:= 100, pprec := m, disc_start := 5)
    for D in [disc_start..disc_bd] do
	/* if square-free discriminant */
	if IsFundamentalDiscriminant(D) and SquareFreeFactorization(D) eq D then
	    try
		batch_compute_p(prime_bd,D : m := m, pprec:= pprec);
	    catch e
		print "trying with higher precision";
		try
		    batch_compute_p(prime_bd,D : m := 2*m, pprec:= 2*pprec);
		catch e2
		    print "could not find GS unit for discriminant", D;
		end try;	  
	    end try;
	end if;
    end for;
    return 0;
end function;


function GS_red_mod_p(D,p,P)

    F<a> := QuadraticField(D);
    H := AbsoluteField(ext<F | P>);
    O := MaximalOrder(H);
    /* pick an arbitrary prime above p */
    frakP := Factorisation(p*O)[1][1];
    Fp, phi := Completion(H,frakP);
    /* zeta := Roots(CyclotomicPolynomial(p^2-1),Fp)[1][1]; */

    FFp := ResidueClassField(IntegerRing(Fp));
    for r in Roots(P,H) do
	u := phi(r[1]);
	v := u*p^-Valuation(u);
	FFp!v;
    end for;

    return FFp;
    
end function;

function GSHigherLevel (Q,p,m : pprec := m)
    nterms := m;
    /* p := 5; */
    /* D := 48; */
    D := Discriminant(Q);
    f := Conductor(QuadraticForms(D));
    print "conductor = ", f;
    print "quadratic form", Q;
    print "Diagonal restriction of this equals:";
    Diagonal_Restriction(Q,1,nterms : Stabilisation := p);
	  
    F := QuadraticField(D);
    Drd := Diagonal_Restriction_Derivative(Q,p,nterms); 
    G := OrdinaryProjection(Drd : f := f);
    /* CT := Coefficient(Drd,0); */
    return G;

    M := ModularForms(p*f);
    
    Eis := [qExpansion(e,nterms) : e in EisensteinSeries(M)];
    Cusp := Basis(CuspidalSubspace(M),nterms);
    assert #Cusp le 1;		/* makes life easier */
    B := Eis cat Cusp;

    CT, Combo := basis_coordinates(G,B : int := false);
    for i in [1..#B] do
	if Coefficient(B[i],0) eq (p-1)/24 then
	    c := Combo[i]/Combo[#B+1];

	    assert B[i] eq qExpansion(EisensteinSeries(ModularForms(p))[1],nterms);
	    print "Detected coefficient in direction of Eisenstein series", B[i];
	    print c;
	end if;
    end for;
    print "algdepping";
    /* can't be bothered to compute LValVec, so just guessing */
    e := GenusFieldRootsOf1(D);
    h := #ReducedOrbits(QuadraticForms(D));
    for n in [-10..10] do
	LValVec := [-n,n];
	P := GSAlgdep(Exp(e*c)*QQ!(p^n),h,LValVec,ZZ!(D/f^2));
	if P ne 0 then
	    return P;
	end if;
    end for;
    return 0;
end function;
    

function batch_compute_SH(disc_bd, p : m := 25, pprec := m, disc_start := 5, overwrite := false, E := EllCurvesData(p)[1])

    PolQ<x> := PolynomialRing(QQ);
    
    Filename := "SHdata/D" * IntegerToString(disc_bd) * "p" *IntegerToString(p) *".csv";
    
    try
	tmp := Read(Filename);
	tmp := 0;
    catch err	
	/* if not specified, start new file */
	Write(Filename, "D,p,X,Y,coefficients");
    end try;

    for D in [disc_start..disc_bd] do
	/*if D fund disc and  p inert in Q(sqrt(D)) */
	found_flag := false;
	computed_flag := false;
	if IsGSDisc(D,p) then
	    /* now check if we added it already */
	    if not overwrite then
		file := Read(Filename);
		pos := Position(file, Sprint(D)* ", "* Sprint(p));
		if pos gt 0 then /* pos eq 0 iff not found */
		    /* print pos; */
		    while file[pos] ne "\n" do
			if file[pos] eq "x" then
			    print "already computed for D,p =", D, ",", p;
			    computed_flag := true;
			    break;
			end if;
			pos +:= 1;
		    end while;
		end if;
	    end if;
	    
	    if not computed_flag then
		Orbs := Reverse(ReducedOrbits(QuadraticForms(D)));
		lprec := pprec;
		while not found_flag do
		    for O in Orbs do
			Q, L := SHPoints(O[1], p,lprec : E := E, pprec:=pprec);
			/* returns E!0, [] if it doesn't find anything */
			if Q ne Parent(Q)!0 then
			    X := MinimalPolynomial(Q[1]);
			    Y := MinimalPolynomial(Q[2]);
			   
			    found_flag := true;
			    newStr := Sprint(D)* ", "* Sprint(p) *", "*Sprint(X)*", "*Sprint(Y)*", "*Sprint(L);
			    overwriteLine(Filename,Sprint(D)* ", "* Sprint(p),newStr);
			   
			end if;

	   
		    end for;
		    /* if this didn't work, reset */
		    lprec +:= 20; /* bump precision if we can't find any */
		    if lprec gt 4*m then /* give up at a certain point */
			break;
		    end if;
		end while;
		if not found_flag then
		    print "could not find SH point for discriminant", D;		   
		    if Position(Read(Filename), Sprint(D)* ", "* Sprint(p)) eq 0 then
			String := Sprint(D)* ", "* Sprint(p) *", NA,NA,NA";
			Write(Filename, String);
		    end if;
		end if;
	    end if;
	end if;
    end for;
    return 0;
end function;
