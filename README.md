# Computing Gross-Stark units from constant terms of Hilbert modular forms


## Description

This repository contains code for computing _Gross-Stark units_ and _Stark-Heegner points_ using the diagonal restriction derivative from [DPV2](https://arxiv.org/abs/2103.02490), as described in [D-J23](https://arxiv.org/abs/2301.08977).

## Getting Started

### Dependencies

* Some version of [magma](http://magma.maths.usyd.edu.au/magma/)

### Installing

* Simply clone (or copy) the repository into your favourite folder.

### Executing programme

* To load the code, move to the directory containing `main.m`, run magma, and then
  ```
  AttachSpec("spec");
  ```
	This imports the main function `GSUnit`, which takes as input an indefinite quadratic form $F$ with discriminant $D$, a prime $p$ inert in $\mathbb{Q}(\sqrt{D})$ and an integer parameter $m$, the number of terms computed of the modular form whose constant term contains the Gross-Stark unit. 

	TODO: decide this parameter automatically and only ask for pprec.
	
One can then compute the Gross-Stark attached to a quadratic form $Q$ as follows:
``` magma
Q := QuadraticForms(33)!<-2,3,3>;
p := 5;
GSUnit(Q,p,30);
```

Similarly, we can find Stark-Heegner points:

``` magma
Q := QuadraticForms(24)!<-2,4,1>;
p := 11;
SHPoints(Q,p,30);
```

* The file `examples.m` contains functions for tabulating Gross-Stark units, and data for primes less than $20$ and discriminants less than $10000$ can be found in the directory called [data](https://github.com/havarddj/drd/tree/main/data).


<!-- ## Experiments with higher level -->
<!-- ### Nonvanishing of diagonal restriction -->
<!-- We can numerically test the conjecture made in DPV2 that the results extend to ring class characters. In this case, the diagonal restriction $f$ does not vanish in general (although it does in certain cases, for example for $D = 84$, in which case $\operatorname{Cl}^+ = \operatorname{Cl}_{(2)}^+$): -->

<!-- ``` magma -->
<!-- Diagonal_Restriction(D48F1,1,30); \\ has conductor 2 -->
<!-- \\ This should return something like $f = 8q + 8q^2 + 32q^3 + 8q^4 + 48q^5 + O(q^6)$. -->
<!-- ``` -->


<!--  However, the average, or "trace", of this over coset representatives for $\Gamma_0(2)$ in $\operatorname{SL}_2(\mathbb Z)$ equals $0$. One can show that this commutes with $p$-stabilisation when $p$ does not divide the conductor, as well as with the $U_p$-operator, so it is plausible (although not proven yet) that we can compute the spectral expansion of the ordinary projection of the diagonal restriction derivative of $f$, and then take the trace. In particular, we hypothesise that the pairing $\langle f,E_{2,N}^{(p)}\rangle$, where the latter is the Eisenstein series on $\Gamma_0(N)$, is the $p$-adic logarithm of some Gross-Stark unit in the ring class field of conductor $N$ of $\mathbb Q(\sqrt {48}) = \mathbb Q(\sqrt 3)$. -->
 
<!-- **I think this example might be problematic because 2 is ramified in F!** -->
<!-- ``` -->
<!-- nterms := 30; -->
<!-- p := 5; -->
<!-- D := 48; -->
<!-- f := Conductor(QuadraticForms(D)); -->
<!-- Q := ReducedOrbits(QuadraticForms(D))[1][1]; -->
<!-- Drd := Diagonal_Restriction_Derivative(Q,p,nterms);  -->
<!-- G := OrdinaryProjection(Drd : f:= f); -->

<!-- F := QuadraticField(D); -->
<!-- Hf<r> := NumberField(RayClassField(Integers(F)*f,[1,2])); -->
<!-- h := Degree(Hf); -->
<!-- print "Degree of ring class field over Q:", 2*h; -->
<!-- ``` -->

<!--  **The rest of the section is probably not quite right; we need to compute the trace, not solve for constant term in terms of the Eisenstein series. What we should do is the following:** -->
<!-- Show that $M_2(\Gamma_0(10))$ is spanned by the new Eisenstein series, the old Eisenstein series from level 5, and the old Eisenstein series of level 2. Then find component in direction of level 5.  -->

<!-- In fact, magma can find all of these at once by running `EisensteinSeries(ModularForms(10));`. Conveniently, these are normalised just like in DPV.  -->

<!-- ``` -->
<!-- M := ModularForms(10); -->

<!-- B := [qExpansion(e,nterms) : e in EisensteinSeries(M)]; -->

<!-- CT, Combo := basis_coordinates(G,B : int := false); -->
<!-- // By inspection, the second Eisenstein series is on level 5, so: -->
<!-- c := Combo[2]/Combo[4]; -->
<!-- ``` -->

<!-- Now the variable $c$ contains $\langle f,E_{2,N}^{(p)}\rangle$, and DPV2 conjectures that if $e = \# \mu(H_N)$, then $e\exp_p(CT)$ is a $p$-unit.  -->

<!-- ``` magma -->
<!-- e := Order(TorsionSubgroup(UnitGroup(AbsoluteField(Hf))));  -->
<!-- print "Number of roots of unity in ring class field:", e; -->
<!-- Delta0 := Discriminant(Integers(AbsoluteField(Hf))); -->

<!-- RKp := PolynomialRing(Parent(CT)); -->
<!-- zeta := Roots(RKp!CyclotomicPolynomial(p^2-1))[1][1]; -->
<!-- for k := 0 to EulerPhi(p^2-1) do -->
<!-- 	for n in [-10..10] do 	 -->
<!-- 		P := algdep(e*zeta^k*Exp(c)*p^n, h); -->
<!-- 		if Degree(P) gt 0 and IsIrreducible(PolynomialRing(F)!P) and Discriminant(Integers(AbsoluteField(ext<F | P>))) mod D eq 0 then -->
<!-- 			fac := Factorisation(Coefficient(P,0)); -->
<!-- 			if #fac le 2 then -->
<!-- 				Delta := Discriminant(Integers(AbsoluteField(ext<F|P>))); -->
<!-- 				print P, "fact of disc:", Factorisation(Delta); -->
<!-- 			end if;			 -->
<!-- 		end if; -->
<!-- 	end for; -->
<!-- end for; -->
<!-- ``` -->

<!-- ``` magma -->
<!-- e := Order(TorsionSubgroup(UnitGroup(AbsoluteField(Hf))));  -->
<!-- print "Number of roots of unity in ring class field:", e; -->
<!-- Delta0 := Discriminant(Integers(AbsoluteField(Hf))); -->

<!-- RKp := PolynomialRing(Parent(c)); -->
<!-- zeta := Roots(RKp!CyclotomicPolynomial(p^2-1))[1][1]; -->
<!-- for k := 0 to EulerPhi(p^2-1) do -->
<!-- 	P := algdep(zeta^k*Exp(c)/2, h); -->
<!-- 	print P;	 -->
<!-- end for; -->
<!-- ``` -->


<!-- ``` magma -->
<!-- nterms := 50; -->
<!-- p := 7; -->
<!-- D := 825; -->
<!-- f := Conductor(QuadraticForms(D)); -->
<!-- Q := ReducedOrbits(QuadraticForms(D))[1][1]; -->
<!-- Drd := Diagonal_Restriction_Derivative(Q,p,nterms);  -->

<!-- F := QuadraticField(D); -->
<!-- Hf<r> := NumberField(RayClassField(Integers(F)*f,[1,2])); -->
<!-- h := Degree(Hf); -->

<!-- algdep(Coefficient(Drd,0),2*h) -->

<!-- ``` -->
<!-- ## Help -->

<!-- Any advice for common problems or issues. -->
<!-- ``` -->
<!-- command to run if program contains helper info -->
<!-- ``` -->

## Author

[Håvard Damm-Johnsen](https://users.ox.ac.uk/~quee4127/)



## License

This project is licensed under the GPL License - see the LICENSE.md file for details

## Acknowledgments

This is based on code by [Jan Vonk](https://github.com/JBVonk) and [Alan Lauder](https://people.maths.ox.ac.uk/lauder/), as well as their papers (with and without collaborators).
