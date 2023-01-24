/* AttachSpec("spec"); */
/* Attach "./src/algdep.m"; */
/* Attach "./src/meyer.m"; */
/* Attach "./src/lindep.m"; */
/* Attach "./src/discs.m"; */
/* Attach "./src/tate_unif.m"; */
/* Attach "./src/overconvergent.m"; */
/* Attach "./src/diagres.m"; */
/* Attach "./src/stark-heegner.m"; */


ZZ := Integers();
QQ := Rationals();
intrinsic GSUnit(F::QuadBinElt, p::RngIntElt, m::RngIntElt : pprec:=m) -> RngUPolElt
{Compute Gross-Stark unit}
    D := Discriminant(F);
    print "- - - - - - - - - - - - - - - - - - - - - - - - ";
    print "Applying GS algo to discriminant", D, "with p-adic precision", pprec;
    assert KroneckerSymbol(D,p) eq -1; /* p inert */

    /* DRD := Diagonal_Restriction_Derivative(F,p,m : pprec := 400); */
    DRD := Diagonal_Restriction_Derivative(F,p,m : pprec := pprec);

    ct := Coefficient(DRD,0);

    print "Constant term equals", ct;
    Orbs := ReducedOrbits(QuadraticForms(D));

    /* To compute the valuation of the constant term, our choice of
    normalisation is precisely so that the constant term is p^R where
    R is the sum of the positive slopes of the vector of L-values */

    e := GenusFieldRootsOf1(D);
    print "Number of roots of unity in NHCF:", e;
    Lvals := [];
    for orb in Orbs do
	Q := orb[1];	
	print Q, "has Meyer special value equal to ", Meyer2(Q);
	ord := ZZ!(Meyer2(Q)*e);
	Append(~Lvals,ord);
    end for;
    
    expt := (ZZ!(Meyer2(F)*e));
    print "p-valuation of GS unit =", expt;
    return GSAlgdep(Exp(e*ct)*QQ!(p^expt), #Orbs, Lvals, D);

end intrinsic;
