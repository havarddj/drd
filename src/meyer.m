intrinsic PellSolution(D::RngIntElt) -> Any
{returns (|t|,u) where epsilon := (t+u sqrt(D))/2
    is a fundamental unit of positive norm in Q(sqrt(D))}

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
    
    /* U1 := Integers()!(Sqrt(Integers!((t^2-4)/D))); /\* NB precision error here *\/ */
    /* assert U1 eq u; */
    assert t^2 - D*u^2 eq 4;
    
    return t,u;

end intrinsic;


intrinsic Automorph(F::QuadBinElt) -> AlgMatElt
{Return generator of stabiliser of positive fundamental unit in real quadratic field attached to F}
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
	
end intrinsic;

function B1(a)
    if a eq Floor(a) then
	return 0;
    end if;
    return a - Floor(a) - 1/2; 
end function;

intrinsic DedekindSumFast(a::RngIntElt,c::RngIntElt) -> FldRatElt
{Compute Dedekind sum s(a,c) using algorithm from Knuth's book}
    assert c ne 0 and GCD(a,c) eq 1;
    if c lt 0 then
	return DedekindSumFast(a,-c);
    end if;
    if a lt 0 or a gt c then
	return DedekindSumFast(a mod c, c);
    end if;
    if c eq 1 then
	return 0;		/* then k/c is an integer */
    end if;
    /* now we're in the situation of Apostol Mod forms ex. 3.10 */
    /* run euclidean algo: */
    x := a;
    y := c;
    R := [];
    while y ne 0 do
	t := y;			/* r_k-1 */
	y := x mod y;		/* r_k+1 */
	x := t;			/* r_k */
	Append(~R, t);
    end while;
    return &+[(-1)^(j+1) *(R[j+1]^2 + R[j]^2+1)/(R[j+1]*R[j]) : j in [1..#R-1] ]/12 -((-1)^#R + 1)/8;
end intrinsic;


function DedekindSum2(a,c)
    /* Defn from Duke-Imamoglu-Toth */

    assert c ne 0 and GCD(a,c) eq 1;
    sum := 0;
    for k in [1..Abs(c)] do
	sum +:= B1(a*k/c)*B1(k/c);
    end for;
    return sum;
end function;


intrinsic Meyer2(F::QuadBinElt) -> FldRatElt
{Compute value of L(0,1_(A-A*)) using Meyer's theorem}
    /* Functioning version, based on Rademacher-Grosswald and DIT18 */
    M := Automorph(F);
    a := M[1][1];
    b := M[1][2];
    c := M[2][1];
    d := M[2][2];
    /* print "c,d =", c,d; */
    if c eq 0 then
	Phi := b/d;
    else
	/* Phi := (a+d)/c - 12*Sign(c)*DedekindSum(d,Abs(c)); */
	/* computing dedekind sum */
	Phi := (a+d)/c - 12*Sign(c)*DedekindSumFast(a,c);
    end if;
    
    Psi := Phi - 3*Sign(c*(a+d));

    return Psi/12;		/* should be Psi/6, just checkin */
    /* Note: computing value of L(0,1_A-A*), which is twice the
       zeta_-(0,A) in Duke-Imamoglu-Toth */
end intrinsic;


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
