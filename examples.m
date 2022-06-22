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

    pval := ZZ!(Meyer2(Q)*GenusFieldRootsOf1(D));
    print "pval equals", pval;

    f := algdep(beta*p^pval,clno);
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
    for l in [0..(p^2-2)] do
	print "Image of beta*zeta^l + 1/zeta*beta^l for l = ", l," equals", beta*zeta^l + 1/(beta*zeta^l);
    end for;
    /* Coefficients(psi(eps)); */
    return 0;
end function;

function temp()
    K := QuadraticField(321);
    R<x> := PolynomialRing(QQ);
    f := 16807*x^6 - 88200*x^5 + 204624*x^4 - 266219*x^3 + 204624*x^2 - 88200*x + 16807;
    H<u> := ext<K | f>;
    zeta := Roots(x^2-x+1,H)[1][1];

    for i := 0 to 5 do
	g := MinimalPolynomial(u*zeta^i);
	print i, GaloisGroup(ext<K | Evaluate(R!g,x^3)>), "\n";
    end for;
		       
end function;
