function PellSolution(D)
    /* returns (|t|,u) where epsilon := (t+u sqrt(D))/2
    is a fundamental unit of positive norm in Q(sqrt(D)) */
    QQ := QuadraticForms(D);
    O := QuadraticOrder(QQ);
    eps := FundamentalUnit(O);
    if Norm(eps) eq 1 then
	t := Abs(Trace(eps));
    else
	t := Abs(Trace(eps^2));
    end if;
    bool, U := IsSquare((t^2-4)/D);
    u := Integers()!U;
    
    U1 := Integers()!(((t^2-4)/D)^(1/2));
    assert U1 eq u;
    assert t^2 - D*u^2 eq 4;
    
    return t,u;

end function;


function Automorph(F)
    ZZ := Integers();
    D := Discriminant(F);
    t,u := PellSolution(D);
    a := F[1];
    b := F[2];
    c := F[3];
    M := Matrix([[ZZ!((t+b*u)/2),c*u],[-a*u,ZZ!((t-b*u)/2)]]);
    assert Determinant(M) eq 1;
    assert F*M eq F;

    return M;
	
end function;

function B1(a)
    if a eq Floor(a) then
	return 0;
    end if;
    return a - Floor(a) - 1/2; 
end function;

function DedekindSum(h,k)
    /* With notation from Rademacher-Grosswald, assumes k =|c| positive */
    assert k ge 1 and GCD(h,k) eq 1;

    return &+[B1(h*mu/k)*B1(mu/k) : mu in [1..k]];

end function;


function DedekindSum2(a,c)
    /* Defn from Duke-Imamoglu-Toth */
    assert c ne 0 and GCD(a,c) eq 1;
    return &+[B1(a*k/c)*B1(k/c) : k in [1..Abs(c)]];
end function;

function Meyer(F)
    /* Non-functioning version */
    print("oops this doesn't give the right answer");
    M := Automorph(F);
    if M[2][1] le 0 then
	M := -M;
    end if;
    		   
    a := M[1][1];
    b := M[1][2];
    c := M[2][1];
    d := M[2][2];
    assert c ge 0;

    assert GCD(c,d) eq 1;
    nA := (a + d)/c - 3 - 12*DedekindSum(d,c);
    return nA/3;
    /* This is eq (17) of Zagier's Asterisque paper, and seems about right*/
    /* 14/02: we have to divide by 2 it seems */
end function;

function Meyer2(F)
    /* Functioning version, based on Rademacher-Grosswald and DIT18 */
    M := Automorph(F);
    		   
    a := M[1][1];
    b := M[1][2];
    c := M[2][1];
    d := M[2][2];

    if c eq 0 then
	Phi := b/d;
    else
	/* Phi := (a+d)/c - 12*Sign(c)*DedekindSum(d,Abs(c)); */
	Phi := (a+d)/c - 12*Sign(c)*DedekindSum2(a,c);
    end if;
    
    Psi := Phi - 3*Sign(c*(a+d));

    return Psi/6;
    /* Note: computing value of L(0,1_A-A*), which is twice the
       zeta_-(0,A) in Duke-Imamoglu-Toth */
end function;


function testMeyer2(F)
    O := ReductionOrbit(F);
    for Q in O do
	print Q;
	print "Meyer2 of ", Q, "equals", Meyer2(Q);

    end for;
    /* assert [Meyer2(F) : Q in O] eq [Meyer2(Q) : Q in O]; */
    return true;
end function;

function AntiguousForm(F)
    D := Discriminant(F);
    return QuadraticForms(D)!<-F[1],F[2],-F[3]>;
end function;

function LValVec(D : forms := [])
    vec := [];
    if forms eq [] then
	for Orb in ReducedOrbits(QuadraticForms(D)) do
	    F := Orb[1];
	    Append(~vec, Meyer2(F));
	end for;
    else
	for Q in forms do
	    F := QuadraticForms(D)!<Q[1],Q[2],Q[3]>;
	    Append(~vec, Meyer2(F));
	end for;
    end if;
    return vec;
    
end function;

/* function Meyer(Q) */
/*     /\* D := Discriminant(Q); *\/ */
/*     /\* K<sqrtD> := QuadraticField(D); *\/ */
/*     a := Q[1]; */
/*     b := Q[2]; */
/*     c := Q[3]; */
/*     /\* Q2 := Parent(Q)!<c,-b,a>; *\/ */
/*     /\* if (-b + Sqrt(D))/a lt 0 then *\/ */
/*     /\* 	w := (-b - sqrtD)/(2*a); *\/ */
/*     /\* else *\/ */
/*     /\* 	w := (-b + sqrtD)/(2*a); *\/ */
/*     /\* end if; *\/ */
/*     /\* return ContinuedFraction(w : Bound :=500); *\/ */
/*     print Q, Q2, IsEquivalent(Q,Q2 : Narrow := true); */
/*     print #NearlyReducedForms(Q), #NearlyReducedForms(Q2); */
/*     return #NearlyReducedForms(Q) - #NearlyReducedForms(Q2); */
/* end function; */
