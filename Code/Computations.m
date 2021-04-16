load "~/Classification_of_Entanglements/AuxillaryFiles/Group_functions.m";

//Page 9 computations
G26 := GL(2,Integers(26));
SG26 := [h`subgroup : h in Subgroups(G26) | FullDeterminantMap(h`subgroup) and ContainsComplexConjugation(h`subgroup)];
for G in SG26 do
	boo, entlev, enttype, NabG := RepresentsPrimitiveEntanglement(G);
	if boo and enttype[1] eq "C3" and enttype[2] ne "C1" then
		assert not IsGen0(G) and not IsGen1(G);
	end if;
end for;


//Fake CM Computations
Cartans := [ ["3Nn", "5Nn"], ["3Nn", "5Ns"], ["3Nn", "7Ns"] ];
for pair in Cartans do
	printf "Working on the pair %o\n", pair;
	G1 := Groups[pair[1]]`group;
	G2 := Groups[pair[2]]`group;
	n1 := #BaseRing(G1);
	n2 := #BaseRing(G2);
	n := n1*n2;
	G := ChangeLevel(G1,n) meet ChangeLevel(G2,n);
	SG := [h`subgroup : h in Subgroups(G) | FullDeterminantMap(h`subgroup) and ContainsComplexConjugation(h`subgroup)];
	for H in SG do
		boo, entlev, enttype, NabG := RepresentsPrimitiveEntanglement(H);
		if boo then
			assert not IsGen0(H) and not IsGen1(H);
		end if;
	end for;
end for;

Borels := [ ["3Nn", "5B"], ["3Ns", "5B"] ];
for pair in Borels do
	printf "Working on the pair %o\n", pair;
	G1 := Groups[pair[1]]`group;
	G2 := Groups[pair[2]]`group;
	n1 := #BaseRing(G1);
	n2 := #BaseRing(G2);
	n := n1*n2;
	G := ChangeLevel(G1,n) meet ChangeLevel(G2,n);
	GLn := GL(2,Integers(n));
	GL1,pi1 := ChangeRing(G,Integers(n1));
	GL2,pi2 := ChangeRing(G,Integers(n2));
	SG := [h`subgroup : h in Subgroups(G) | FullDeterminantMap(h`subgroup) and ContainsComplexConjugation(h`subgroup)];
	for H in SG do
		boo, entlev, enttype, NabG := RepresentsPrimitiveEntanglement(H);
		if boo and pi1(H) eq G1 and pi2(H) eq G2 then
			if IsGen0(H) then
				assert true in {IsConjugate(GLn,H,r`G) : r in [r : r in MaxCleanGenus0WithModels[<[ 3, 5 ], [ "C2", "C2" ]>] | r`label eq pair] };
			end if;
			if IsGen1(H) then
				name, rank := JacobianOfXG(H);
				assert rank eq 0;
			end if;
		end if;
	end for;
end for;

//*************************
//Section 4.9 Computations
//*************************

//We start by defining the generic elliptic curve with a 5-isog. over Q(t).
F<t> := FunctionField(Rationals());
E := EllipticCurve([-27*(t^2 + 10*t + 5)^3*(t^2 - 20*t - 25)^-2*(t^2 + 22/25*t + 1/5)^-1,54*(t^2 + 10*t + 5)^3*(t^2 - 20*t - 25)^-2*(t^2 + 22/25*t + 1/5)^-1]);
f5 := DivisionPolynomial(E,5);
fac5 := Factorization(f5);
f51 := fac5[1][1];
assert Degree(f51) eq 2;

/*
Since f51 is quadratic adjoining a root is the same as
adjoining the square root of its discriminant.
*/

Df51 := Discriminant(f51);
delta := 5*(t^2 + 22/25*t + 1/5);
assert IsSquare(delta*Df51);
m := (t+7/25); n := (2*t+24/25);
assert m^2+n^2 eq delta;

//Thus, if sqrt(d) is in the field of definition of the kernel of the 5-isogeny… give the isogeny a name. phi or something… Sheesh.

K<sqrtdelta> := ext< F | Polynomial([-delta,0,1]) >;
a1 := Roots(ChangeRing(f51,K))[1][1];


//Now we define L=Q(P)=L1 to check our work.

R<y> := PolynomialRing(K);
g51 := Evaluate(DefiningPolynomial(E),[a1,y,1]);
L<b> := ext<K | g51>;
P := BaseChange(E,L)![a1,b];
Order(P) eq 5;




//*************************
//Lemma 4.15
//*************************

//We start by defining the generic elliptic curve with a 7-isog. over Q(t).

F<t> := FunctionField(Rationals());
E := EllipticCurve([-27*(t^2 + 13*t + 49)^3*(t^2 + 245*t + 2401), 54*(t^2 + 13*t + 49)^4 * (t^4 - 490*t^3 - 21609*t^2 - 235298*t - 823543)]);

//Lets get out hands on the lon fact of degree 3 of the 7-division polynomial.
f7 := DivisionPolynomial(E,7);
fac7 := Factorization(f7);
f71 := fac7[1][1];
assert Degree(f71) eq 3;

//Lets see that f71 and g define the same cyclic cubic field.

P<x> := PolynomialRing(F);
g := x^3 + 147*(t^2 + 13*t + 49)*x^2 + 147*(t^2 + 13*t + 49)*(33*t^2 + 637*t + 2401)*x+49*(t^2 + 13*t + 49)*(881*t^4 + 38122*t^3+525819*t^2+3058874*t+5764801);
assert IsSquare(Discriminant(g));
K1 := ext< F|g >;
assert not IsIrreducible(ChangeRing(f71,K1));

// The last setp is to show that g and f are related as we claimed

s := 49/t+8;
f := x^3-s*x^2+(s-3)*x+1;
assert IsIrreducible(f);
assert not IsIrreducible(ChangeRing(f,K1));

//******************
//Proposition 5.2
//******************

E1 := EllipticCurve("256a1");
E2 := QuadraticTwist(E1,2);
E3 := QuadraticTwist(E1,-2);
E4 := QuadraticTwist(E1,-1);
Universe := [E1,E2,E3,E4];


for E in Universe do
	f8 := DivisionPolynomial(E,8) div DivisionPolynomial(E,4);
	F := SplittingField(f8);
	assert Degree(F) eq 32;
	rts := Roots(ChangeRing(f8,F));
	P<y> := PolynomialRing(F);
	for rt in rts do
		r := rt[1];
		yPol := Evaluate( DefiningPolynomial( ChangeRing( E,F )) , [r,y,1]);
		assert not IsIrreducible(yPol);
	end for;
end for;

PQ<x> := PolynomialRing(Rationals());
f4<x> := x^8+6*x^4+1;
K1<a1> := SplittingField(f4); // Q(x(E[4]))
sqrt2 := 1/2*(a1^4 + 3);
assert sqrt2^2 eq 2;
P<d> := FunctionField(K1);


K<a> := ext<P | Polynomial([-d*(2+sqrt2), 0, 1]) >;
E1K := ChangeRing( EllipticCurve("256a1") , K );
E2K := ChangeRing( QuadraticTwist(E1,2) , K );
E3K := ChangeRing( QuadraticTwist(E1,-2) , K );
E4K := ChangeRing( QuadraticTwist(E1,-1) , K );

assert GroupName(pPowerTorsion(QuadraticTwist(E1K,d),2)) eq "C4^2";
assert GroupName(pPowerTorsion(QuadraticTwist(E2K,d),2)) eq "C4^2";
assert GroupName(pPowerTorsion(QuadraticTwist(E3K,d),2)) eq "C4^2";
assert GroupName(pPowerTorsion(QuadraticTwist(E4K,d),2)) eq "C4^2";

//  "A straight forward computations" in Proposition 5.4

K<a> := QuadraticField(-3);
F1<s> := FunctionField(K);
F2<sqrts> := ext< F1| Polynomial([-s,0,1]) >;
F3<cubert4s> := ext< F2| Polynomial([4*s,0,0,1]) >;
E := EllipticCurve([0,F3!s]);
P1 := E![0,F3!sqrts];
P2 := E![cubert4s,a*sqrts];
assert Order(P1) eq 3 and Order(P2) eq 3;
for n in [0,1,2] do
	assert n*P1 ne P2;
end for;


