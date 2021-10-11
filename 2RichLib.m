////////////////////////////////////////////////////////////////////////
////	I require functions that are taken from Magma libraries,    ////
////	so please ensure that the path here is correct.		    ////
////////////////////////////////////////////////////////////////////////
import "/usr/local/magma/package/Geometry/CrvG2/richelot.m" : padseq, linear_interpolate, rich_codomain_deg5, rich_codomain_deg6, deg4_quadratic_norm_decompositions, sing_rich_codomain;


////	Writing my own cubic root code...
CubeRoot := function( R )
	_<x> := PolynomialRing(Parent(R));
	CubicRts := Roots(x^3-R);
	if IsEmpty(CubicRts) then
		return 0;
	else
		return CubicRts[1,1];
	end if;
end function;

////    Obtain Weierstrass points of a hyperelliptic curve
WeierstrassPoints := function( C )
        F,_ := HyperellipticPolynomials(C);
        Rts := Roots(F);
        WPts := [ C![R[1],0,1] : R in Rts ];
        if #WPts eq 6 then
                return WPts;
        elif #WPts eq 5 then
                WPts := WPts cat [ P : P in PointsAtInfinity(C)];
                return WPts;
        elif #WPts eq 2 or #WPts eq 4 then
                R<x> := Parent(F);
                k := BaseRing(F);
                L := ext<k|2>;
                S<x> := ChangeRing( R, L );
                Rts := Roots(S!F);
                C := BaseChange( C, L);
                WPts := [ C![R[1],0,1] : R in Rts ];
                if #WPts eq 6 then
                        return WPts;
                end if;
        end if;
        return 0;
end function;

////    Given generators of a (2,2)-subgroup in mumford representations, 
////    we need to recover the 3 weierstrass points associated to this subgroup.
MumfordSubgroupToQuadraticSplitting := function( D, J )
        if J ne Parent(D[1]) or J ne Parent(D[2]) or J ne Parent(D[3]) then
                error "MumfordSubgroupToWeierstrassPoints: D's are not in the same jacobian.";
        end if;

	f,g := HyperellipticPolynomials(Curve(J));
	lc:=LeadingCoefficient(f);
	CR := CubeRoot(lc);
	if g ne 0 then; error "MumfordSubgroupToQuadraticSplitting: Check model of curve. Works only for simplified model"; end if;
	lc := LeadingCoefficient(f);

	Gi := [ CR*D[1,1], CR*D[2,1], CR*D[3,1] ];
	if f eq &*Gi then;	return Gi;
	else 			return [];
	end if;
end function;

////	Given a quadratic splitting, we know that this corresponds 
////	to a (2,2)-subgroup. So we want to recover this subgroup.
QuadraticSplittingToMumfordSubgroup := function( Gi )
	C := HyperellipticCurve(&*Gi);
	J := Jacobian(C);
	MumSubGrp := [];
	k := BaseRing(C);
        for G in Gi do
		xs := Roots(G);
		if IsEmpty(xs) then
			xs := Roots(PolynomialRing(ext<k|2>)!G);
		end if;
		R<x> := PolynomialRing(Parent(xs[1,1]));
		Append( ~MumSubGrp, J![(x-xs[1,1])*(x-xs[2,1]),0] );
	end for;
        return MumSubGrp;
end function;

////	To get a (2,2)-subgroup, we need to make sure that the first component
////	of the mumford representations of the 3 points are coprime. This
////	function checks for that.
Is_22_Subgroup := function( KerTors )
	if #KerTors ne 3 then
		error "Is_22_Subgroup: Wrong number of points on input";
	end if;
	J := Parent(KerTors[1]);
	if (J ne Parent(KerTors[2])) or (J ne Parent(KerTors[3])) then
		error "Is_22_Subgroup: KerTors are not in the same Jacobian";
	end if;

	return (not IsEmpty(MumfordSubgroupToQuadraticSplitting( KerTors, J )));
end function;

////    Given G's we return H's
GiToHi := function ( Gi )
	delta:=Determinant(Matrix([Eltseq(g): g in Gi]));
	Hfunc:=func<a,b|Determinant(Matrix([[Derivative(a),Derivative(b)],[a,b]]))/delta>;
        return [Hfunc(Gi[i[1]],Gi[i[2]]): i in [[2,3],[3,1],[1,2]]];
end function;

////	Helper function to allow us to specify kernels of 
////	Richelot isogenies in terms of Jacobian elements.
MumfordSubgrpToQuadinCubicAlg_deg5 := function( Tors )
	J := Parent(Tors[1]);
        C := Curve(J);
	f,g := HyperellipticPolynomials(C);
	R<x> := Parent(f);

	if (Degree(f) ne 5) or (g ne 0) then
		error "MumfordSubgrpToQuadinCubicAlg_deg5: Degree of f is wrong and/or model of curve is not simplified.";
	end if;

        ////    Find partner of point at infinity
	for ind in [1,2,3] do
		if Degree(Tors[ind,1]) eq 1 then
			r := Roots(Tors[ind,1])[1,1];
		end if;
	end for;
	Deg4Tors := [ D : D in Tors | Degree(D[1]) eq 2 ];
	fct1 := Factorisation(Deg4Tors[1,1]);
	fct2 := Factorisation(Deg4Tors[2,1]);
	g := linear_interpolate( [ fct1[1,1]*fct1[2,1],fct2[1,1]*fct2[2,1] ] );
        return <r,g>;
end function;

////	Helper function to allow us to specify kernels of 
////	Richelot isogenies in terms of Jacobian elements.
MumfordSubgrpToQuadinCubicAlg_deg6 := function( Tors )
	f,g := HyperellipticPolynomials(Curve(Parent(Tors[1])));
	J := Parent(Tors[1]);
	if (Degree(f) ne 6) or (g ne 0) then
		error "MumfordSubgrpToQuadinCubicAlg_deg6: Degree of f is wrong and/or model of curve is not simplified.";
	end if;
        Fi := MumfordSubgroupToQuadraticSplitting( Tors, J );
        return linear_interpolate([Fi[1],Fi[2],Fi[3]]);
end function;

////	My wrapper function for richelot isogenies in magma
////	with kernels given in mumford rep. #KerTors = 3!!
////	!! BEWARE: You cannot use get KerTors such that the 
////	!! quadratic splittings are not monic!!
BoRichelotIsogeny := function ( KerTors )
        J := Parent(KerTors[1]);
        C := Curve(J);
        f := HyperellipticPolynomials(SimplifiedModel(C));
        lc:=LeadingCoefficient(f);

        if Degree(f) eq 5 then
		f := f/lc;
		C1 := HyperellipticCurve(f);
		_,phi := IsIsomorphic(C,C1);
		Ker := [ Evaluate( phi, P ) : P in KerTors ];
                v := MumfordSubgrpToQuadinCubicAlg_deg5( Ker );
                g := rich_codomain_deg5(v[1],v[2]);
		if g eq 0 then;		D := sing_rich_codomain(f,v[2]:r:=v[1]);
                else			D := HyperellipticCurve(lc*g);
		end if;
        elif Degree(f) eq 6 then
                Q := MumfordSubgrpToQuadinCubicAlg_deg6( KerTors );
                g := rich_codomain_deg6(Q);
		if g eq 0 then;		D := sing_rich_codomain(f,Q);
                else D := HyperellipticCurve(lc*g);
		end if;
        end if;
        return D;
end function;

////	Now, we will map point under the Richelot isogeny!
////	The goal is to map a divisor, expressed in mumford representation, and map
////	it under the Richelot isogeny to obtain the divisor in the Richelot
////	codomain. To do that, we will need to find the two points associated to 
////	the given divisor and map those affine points via the Richelot 
////	correspondence to the codomain curve.

////	Given an affine point and the quadratic splittings, return the two points
////	that the affine point maps to under the Richelot isogeny associated to the
////	quadratic splitting.
AffineMap_RichelotCorrespondence := function ( Gi, P )
        X := Curve(P);
        delta:=Determinant(Matrix([Eltseq(g): g in Gi]));
        Hfunc:=func<a,b|Determinant(Matrix([[Derivative(a),Derivative(b)],[a,b]]))/delta>;
        Hi:=[Hfunc(Gi[i[1]],Gi[i[2]]): i in [[2,3],[3,1],[1,2]]];
	H := &*Hi;
        XG := HyperellipticCurve(H);

        k := BaseRing(X);
        S<u1,v1,u2,v2>:=PolynomialRing(k,4);
        Eq1 := Evaluate(Gi[1],u1)*Evaluate(Hi[1],u2) + Evaluate(Gi[2],u1)*Evaluate(Hi[2],u2);
        Eq2 := v1*v2 - Evaluate(Gi[1],u1)*Evaluate(Hi[1],u2)*(u1-u2);

        Qx := Roots(UnivariatePolynomial(Evaluate(Eq1,[P[1],P[2],u2,v2])));
        if IsEmpty(Qx) then
                k := ext<k|2>;
                T<u1,v1,u2,v2>:=PolynomialRing(k,4);
                Eq1_ext := T!Eq1;
                Eq2_ext := T!Eq2;
                Qx:=Roots(UnivariatePolynomial(Evaluate(Eq1_ext,[P[1],P[2],u2,v2])));
        end if;
        Qy := [];
        for ind in [1,2] do
                if UnivariatePolynomial(Evaluate(Eq2,[P[1],P[2],Qx[1,1],v2])) eq 0 then
                        Append( ~Qy, k!0 );
                else
                        Append( ~Qy, Roots(UnivariatePolynomial(Evaluate(Eq2,[P[1],P[2],Qx[ind,1],v2])))[1,1] );
                end if;
        end for;
        XG := BaseChange(XG,Parent(Qx[1,1]));
	if Qx[1,2] eq 1 then
	        return [* XG![ Qx[1,1], Qy[1] ], XG![ Qx[2,1], Qy[2] ] *];
	elif Qx[1,2] eq 2 then
		Qy := Roots( UnivariatePolynomial( v2^2 - Evaluate(H,Qx[1,1]) ) );
		if IsEmpty(Qy) then
			k := ext<k|2>;
			T := PolynomialRing(k);
			QyEq_ext := T!(UnivariatePolynomial( v2^2 - Evaluate(H,Qx[1,1]) ));
			Qy:=Roots(QyEq_ext);
		end if;
		XG := BaseChange(XG,Parent(Qy[1,1]));
		return [* XG![ Qx[1,1], Qy[1,1] ], XG![ Qx[1,1], Qy[2,1] ] *];
	else
		"[Error] AffineMap_RichelotCorrespondence: Check solutions.";
		return [**];
	end if;
end function;

////	This function maps points via an isomorphism
MapMumPtsViaIsom := function( J1, J2, PtsInJ1 )
	IsIso, phi := IsIsomorphic( Curve(J1), Curve(J2) );
	if not IsIso then
		return 0;
	end if;

	PtsInJ2 := [];
	for D in PtsInJ1 do
		Append( ~PtsInJ2, Evaluate(phi,D) );
	end for;
	return PtsInJ2;
end function;

MapMumPtsViaSquareIsom := function( D, JlcSq, lc )
	J := Parent(D);
	IsIso, phi := IsIsomorphic( Curve(J), Curve(JlcSq) );
	if not IsIso then;	return 0;	end if;
	PtsInJlcSq := [];
        return Evaluate(phi,D);
end function;

////	Now, we map!
BoRichIsogMap := function( KerTors, PTs_in_mumford )

	J  := Parent(KerTors[1]);
	k  := BaseField(J);
	C  := Curve(J);
	f  := HyperellipticPolynomials(SimplifiedModel(C));
	R  := Parent(f);
	lc := LeadingCoefficient(f);
	CR := CubeRoot(lc);
	if CR eq 0 then
		f  := lc^2*f;
		C  := HyperellipticCurve(f);
		J  := Jacobian(C);
		CR := lc;
		lc := lc^3;
		postKerTors := [];
		for D in KerTors do
			Append( ~postKerTors, MapMumPtsViaSquareIsom( D, J, lc ) );
		end for;
		postPTs_in_mumford := [];
		for D in PTs_in_mumford do
			Append( ~postPTs_in_mumford, MapMumPtsViaSquareIsom( D, J, lc ) );
		end for;
		KerTors := postKerTors;
		PTs_in_mumford := postPTs_in_mumford;
	end if;
	
	Gi := MumfordSubgroupToQuadraticSplitting( KerTors, J );
	delta := Determinant(Matrix([Eltseq(g): g in Gi]));
	Hfunc := func<a,b|Determinant(Matrix([[Derivative(a),Derivative(b)],[a,b]]))/delta>;
	Hi    := [Hfunc(Gi[i[1]],Gi[i[2]]): i in [[2,3],[3,1],[1,2]]];
	H     := &*Hi;
	JD    := Jacobian(HyperellipticCurve(H));
	ImDiv := [];

	for Div in PTs_in_mumford do
		if (Div in KerTors) or (Div eq J!0) then
			Append( ~ImDiv, JD!0 );
			continue;
		end if;
		ImAff := [**];
		AffineP := MumfordToPT(Div);
		for Pind in AffineP do
			ImAff cat:= AffineMap_RichelotCorrespondence( Gi, Pind );
		end for;
		JD := BaseChange( JD, CommonOverfield(Parent(ImAff[1,1]), Parent(ImAff[3,1]) ) );
		XD := Curve(JD);
		Append( ~ImDiv, JD![ XD!ImAff[1], -XD!ImAff[2] ] + JD![ XD!ImAff[3], -XD!ImAff[4]] );
	end for;

	////	Now, we reduce back to the original field!
	Jret := BaseChange(JD,k);
	phi := Coercion(BaseRing(JD),k);
	ImDivret := [];
	for Div in ImDiv do
		Divret := [ R![ phi(IND) : IND in Eltseq(Div[1]) ], R![ phi(IND) : IND in Eltseq(Div[2]) ] ];
		Append( ~ImDivret, Jret!Divret );
	end for;
	return Jret, ImDivret;
end function;

////	Function returns if two curves are connected by a Richelot isogeny
IsRichelotIsogenous := function( C1, C2  )
        NbC1 := RichelotIsogenousSurfaces(C1);
        for X in NbC1 do
                if Category(X) ne CrvHyp then;  continue;       end if;
                if IsIsomorphic(X,C2) then;     return true;    end if;
        end for;
        return false;
end function;

////	Function returns a Richelot isogeny that joins two curves
FindConnectingKernels := function( C2, C1_2Tors )
        for ind in [1..15] do; for jnd in [1..ind] do;
                Ker := [ C1_2Tors[ind], C1_2Tors[jnd], C1_2Tors[ind]+C1_2Tors[jnd] ];
                if Is_22_Subgroup(Ker) then;    if IsIsomorphic( C2, BoRichelotIsogeny(Ker) ) then;
                        return [jnd, ind];
                end if; end if;
        end for; end for;
end function;


BoKummer2Isogeny := function( KerTors )
	k := BaseRing(Parent(KerTors[1,1]));
	f,_ := HyperellipticPolynomials( Curve( Parent( KerTors[1] ) ) );
	lc := LeadingCoefficient(f);
	if not (KerTors[1,1]*KerTors[2,1]*KerTors[3,1]) eq f/lc then;		error "BoKum2Isog: Not (2,2)-subgroup";		end if;


	Gi := [ KerTors[ind,1] : ind in [1,2,3] ];
        delta:=Determinant(Matrix([Eltseq(g): g in Gi]));
	Hfunc := func<a,b|Determinant(Matrix([[Derivative(a),Derivative(b)],[a,b]]))>;
	Hi    := [Hfunc(Gi[i[1]],Gi[i[2]]): i in [[2,3],[3,1],[1,2]]];
	fhat := &*Hi;

	T := HyperellipticCurve(fhat);
	Chat := QuadraticTwist(T,Delta);
	return T;
end function;

BoKum2IsogMap := function( KerTors, PTs_in_mumford )
	Retuple := [];
	Chat := BoKummer2Isogeny( KerTors );
	J1 := Parent(KerTors[1]);
	J2 := Jacobian(Chat);
	K1 := KummerSurface( J1 );
	K2 := KummerSurface( J2 );
	F0,F1,F2,F3,F4,F5,F6 := Explode( Coefficients( HyperellipticPolynomials( Curve(J1) ) ) );

	for Div in PTs_in_mumford do;

		v3,v2,v1,v0 := Explode(Eltseq(K1!Div));
	
		C0 := 16*v1^4*F0^2*F2*F6-16*v1^4*F0^2*F3*F5-4*v1^4*F0*F1^2*F6+16*v1^4*F0*F2^2*F4-4*v1^4*F0*F2*F3^2-4*v1^4*F1^2*F2*F4-8*v1^3*v0*F0*F3^2-8*v1^3*v0*F1^2*F4+8*v1^2*v0^2*F0*F4-2*v1^2*v0^2*F1*F3-4*v2^4*F0*F2*F5^2-4*v2^4*F1^2*F4*F6+8*v2^2*v0^2*F0*F6-8*v1^3*v2*F1^3*F6+16*v1^2*v2^2*F0^2*F5^2+16*v3^4*F0*F4*F6^2-4*v3^4*F0*F5^2*F6-16*v3^4*F1*F3*F6^2+16*v3^4*F2*F4^2*F6-4*v3^4*F2*F4*F5^2-4*v3^4*F3^2*F4*F6+8*v0^2*v3^2*F2*F6-2*v0^2*v3^2*F3*F5-8*v0*v3^3*F2*F5^2-8*v0*v3^3*F3^2*F6+32*v1^3*v3*F0^2*F5^2+64*v1^2*v3^2*F0^2*F6^2+12*v1^2*v3^2*F1^2*F5^2+32*v1*v3^3*F1^2*F6^2+16*v2^2*v3^2*F1^2*F6^2-8*v2*v3^3*F0*F5^3+v0^4+v1^4*F1^2*F3^2+16*v1^4*F0^2*F4^2-2*v1^4*F1^3*F5+v2^4*F1^2*F5^2+16*v2^4*F0^2*F6^2+8*v1^4*F0*F1*F2*F5-8*v1^4*F0*F1*F3*F4+32*v1^3*v0*F0*F2*F4+16*v2^4*F0*F2*F4*F6+v3^4*F3^2*F5^2-2*v3^4*F1*F5^3+16*v3^4*F2^2*F6^2+16*v2^3*v0*F0*F3*F6-32*v1^3*v2*F0^2*F3*F6+32*v1^3*v2*F0^2*F4*F5+32*v1^3*v2*F0*F1*F2*F6-16*v1^3*v2*F0*F1*F3*F5+32*v1^3*v2*F0*F2^2*F5-8*v1^3*v2*F1^2*F2*F5+32*v1^2*v2^2*F0^2*F4*F6-24*v1^2*v2^2*F0*F1*F3*F6+64*v1^2*v2^2*F0*F2^2*F6+8*v1^2*v2^2*F0*F2*F3*F5-16*v1^2*v2^2*F1^2*F2*F6-2*v1^2*v2^2*F1^2*F3*F5+32*v1*v2^3*F0^2*F5*F6+32*v1*v2^3*F0*F2*F3*F6-8*v1*v2^3*F1^2*F3*F6+48*v1^2*v2*v0*F0*F2*F5-12*v1^2*v2*v0*F1^2*F5+64*v1*v2^2*v0*F0*F2*F6+8*v1*v2^2*v0*F0*F3*F5-16*v1*v2^2*v0*F1^2*F6+8*v1*v2*v0^2*F0*F5+8*v3^4*F1*F4*F5*F6-8*v3^4*F2*F3*F5*F6+32*v0*v3^3*F2*F4*F6-64*v1^3*v3*F0^2*F4*F6+16*v1^3*v3*F0*F1*F3*F6+16*v1^3*v3*F0*F2*F3*F5-4*v1^3*v3*F1^2*F3*F5+96*v1^2*v3^2*F0*F2*F4*F6-32*v1^2*v3^2*F0*F2*F5^2-16*v1^2*v3^2*F0*F3^2*F6+8*v1^2*v3^2*F0*F3*F4*F5-32*v1^2*v3^2*F1^2*F4*F6+8*v1^2*v3^2*F1*F2*F3*F6-64*v1*v3^3*F0*F2*F6^2+16*v1*v3^3*F0*F3*F5*F6+16*v1*v3^3*F1*F3*F4*F6-4*v1*v3^3*F1*F3*F5^2+32*v1^2*v0*v3*F0*F2*F6+16*v1^2*v0*v3*F0*F3*F5-8*v1^2*v0*v3*F1^2*F6+16*v1*v0^2*v3*F0*F6+32*v1*v0*v3^2*F0*F4*F6-8*v1*v0*v3^2*F0*F5^2+16*v1*v0*v3^2*F1*F3*F6+32*v2^3*v3*F0*F1*F6^2+32*v2^3*v3*F0*F3*F4*F6-8*v2^3*v3*F0*F3*F5^2+32*v2^2*v3^2*F0*F2*F6^2-24*v2^2*v3^2*F0*F3*F5*F6+64*v2^2*v3^2*F0*F4^2*F6-16*v2^2*v3^2*F0*F4*F5^2+8*v2^2*v3^2*F1*F3*F4*F6-2*v2^2*v3^2*F1*F3*F5^2-32*v2*v3^3*F0*F3*F6^2+32*v2*v3^3*F0*F4*F5*F6+32*v2*v3^3*F1*F2*F6^2-16*v2*v3^3*F1*F3*F5*F6+32*v2*v3^3*F1*F4^2*F6-8*v2*v3^3*F1*F4*F5^2+64*v2^2*v0*v3*F0*F4*F6-16*v2^2*v0*v3*F0*F5^2+8*v2^2*v0*v3*F1*F3*F6+8*v2*v0^2*v3*F1*F6+48*v2*v0*v3^2*F1*F4*F6-12*v2*v0*v3^2*F1*F5^2+64*v1^2*v2*v3*F0^2*F5*F6-32*v1^2*v2*v3*F0*F1*F4*F6+16*v1^2*v2*v3*F0*F1*F5^2+64*v1^2*v2*v3*F0*F2*F3*F6+8*v1^2*v2*v3*F0*F3^2*F5-8*v1^2*v2*v3*F1^2*F3*F6+64*v1*v2^2*v3*F0^2*F6^2+32*v1*v2^2*v3*F0*F1*F5*F6+48*v1*v2^2*v3*F0*F3^2*F6+64*v1*v2*v3^2*F0*F1*F6^2-32*v1*v2*v3^2*F0*F2*F5*F6+64*v1*v2*v3^2*F0*F3*F4*F6-8*v1*v2*v3^2*F0*F3*F5^2+16*v1*v2*v3^2*F1^2*F5*F6+8*v1*v2*v3^2*F1*F3^2*F6+80*v1*v2*v0*v3*F0*F3*F6+4*v1*v2*v0*v3*F1*F3*F5;
		
		C1 := 4*v1*v0^3-16*v1^4*F0*F2*F4+4*v1^3*v0*F1*F3-16*v1^3*v0*F0*F4-16*v2^4*F0*F4*F6-8*v2^3*v0*F1*F6+4*v1^4*F0*F3^2+4*v1^4*F1^2*F4-16*v1^4*F0^2*F6+4*v1^2*v0^2*F2+4*v2^4*F0*F5^2+4*v3^4*F4*F5^2-16*v3^4*F2*F6^2-16*v3^4*F4^2*F6-12*v0^2*v3^2*F6+8*v0*v3^3*F5^2+8*v1^3*v2*F1^2*F5+12*v1^2*v2^2*F1^2*F6+8*v3^4*F3*F5*F6-32*v0*v3^3*F4*F6-16*v1^3*v3*F1^2*F6+16*v1^2*v3^2*F0*F5^2-16*v1^2*v3^2*F2^2*F6+32*v1*v3^3*F0*F6^2-8*v1*v3^3*F3^2*F6+4*v2^3*v3*F1*F5^2+4*v2^2*v3^2*F2*F5^2+4*v2*v3^3*F3*F5^2-48*v2^2*v3^2*F0*F6^2-32*v2*v3^3*F1*F6^2-4*v2*v0^2*v3*F5-16*v1^3*v2*F0*F1*F6-32*v1^3*v2*F0*F2*F5-64*v1^2*v2^2*F0*F2*F6-8*v1^2*v2^2*F0*F3*F5-32*v1*v2^3*F0*F3*F6-4*v1*v2^2*v0*F1*F5-32*v1^2*v2*v0*F0*F5-48*v1*v2^2*v0*F0*F6+32*v1^3*v3*F0*F2*F6-16*v1^3*v3*F0*F3*F5-48*v1^2*v3^2*F0*F4*F6+24*v1^2*v3^2*F1*F3*F6-8*v1^2*v3^2*F1*F4*F5-16*v1*v3^3*F1*F5*F6-4*v1*v0*v3^2*F3*F5-8*v1^2*v0*v3*F1*F5-16*v1*v0*v3^2*F2*F6-16*v2^3*v3*F0*F5*F6-16*v2^3*v3*F1*F4*F6-8*v2^2*v3^2*F1*F5*F6-16*v2^2*v3^2*F2*F4*F6-16*v2*v3^3*F3*F4*F6-16*v2^2*v0*v3*F2*F6-24*v2*v0*v3^2*F3*F6-4*v1^2*v2*v3*F1*F3*F5-16*v1^2*v2*v3*F0*F4*F5-16*v1^2*v2*v3*F1*F2*F6-16*v1*v2^2*v3*F0*F5^2-24*v1*v2^2*v3*F1*F3*F6-16*v1*v2*v3^2*F0*F5*F6-8*v1*v2*v3^2*F1*F5^2-16*v1*v2*v3^2*F2*F3*F6-24*v1*v2*v0*v3*F1*F6-8*v1*v2*v0*v3*F2*F5;
		
		C2 := 4*v2*v0^3-4*v1^4*F0*F2*F3+4*v1^3*v0*F0*F3-4*v2^4*F0*F3*F6+4*v2^3*v0*F1*F5+32*v1^3*v2*F0^2*F6-4*v1^3*v2*F0*F3^2+4*v1^2*v2^2*F1^2*F5+8*v1*v2^3*F1^2*F6+8*v1*v2*v0^2*F2-4*v3^4*F3*F4*F6+4*v0*v3^3*F3*F6+16*v1^3*v3*F1^2*F5-6*v1^3*v3*F1*F3^2+16*v1^2*v3^2*F1*F4^2+16*v1^2*v3^2*F2^2*F5+16*v1*v3^3*F1*F5^2-6*v1*v3^3*F3^2*F5-8*v1*v0^2*v3*F3+8*v2^3*v3*F0*F5^2+4*v2^2*v3^2*F1*F5^2+32*v2*v3^3*F0*F6^2-4*v2*v3^3*F3^2*F6+8*v2*v0^2*v3*F4+v1^4*F1^2*F3+16*v1^4*F0^2*F5+4*v1^2*v0^2*F1+5*v2^2*v0^2*F3+v3^4*F3*F5^2+16*v3^4*F1*F6^2+4*v0^2*v3^2*F5+5*v1^2*v3^2*F3^3+16*v1^3*v2*F0*F1*F5+32*v1^2*v2^2*F0*F1*F6-4*v1^2*v2^2*F0*F3*F4-4*v1*v2^3*F0*F3*F5+16*v1^2*v2*v0*F0*F4+2*v1^2*v2*v0*F1*F3+8*v1*v2^2*v0*F0*F5+8*v1*v2^2*v0*F1*F4-32*v1^3*v3*F0*F2*F5+16*v1^3*v3*F0*F3*F4-20*v1^2*v3^2*F0*F3*F6-14*v1^2*v3^2*F1*F3*F5-20*v1^2*v3^2*F2*F3*F4-32*v1*v3^3*F1*F4*F6+16*v1*v3^3*F2*F3*F6-16*v1^2*v0*v3*F0*F5+16*v1^2*v0*v3*F1*F4-12*v1^2*v0*v3*F2*F3-16*v1*v0*v3^2*F1*F6+16*v1*v0*v3^2*F2*F5-12*v1*v0*v3^2*F3*F4-4*v2^3*v3*F1*F3*F6+32*v2^2*v3^2*F0*F5*F6-4*v2^2*v3^2*F2*F3*F6+16*v2*v3^3*F1*F5*F6+8*v2^2*v0*v3*F1*F6+8*v2^2*v0*v3*F2*F5+16*v2*v0*v3^2*F2*F6+2*v2*v0*v3^2*F3*F5-64*v1^2*v2*v3*F0*F2*F6-20*v1^2*v2*v3*F0*F3*F5+32*v1^2*v2*v3*F0*F4^2+32*v1^2*v2*v3*F1^2*F6+16*v1^2*v2*v3*F1*F2*F5-12*v1^2*v2*v3*F1*F3*F4-56*v1*v2^2*v3*F0*F3*F6+32*v1*v2^2*v3*F0*F4*F5+32*v1*v2^2*v3*F1*F2*F6-8*v1*v2^2*v3*F1*F3*F5-64*v1*v2*v3^2*F0*F4*F6+32*v1*v2*v3^2*F0*F5^2-20*v1*v2*v3^2*F1*F3*F6+16*v1*v2*v3^2*F1*F4*F5+32*v1*v2*v3^2*F2^2*F6-12*v1*v2*v3^2*F2*F3*F5-48*v1*v2*v0*v3*F0*F6+16*v1*v2*v0*v3*F1*F5+16*v1*v2*v0*v3*F2*F4-10*v1*v2*v0*v3*F3^2;
		
		C3 := 4*v0^3*v3+4*v3^4*F2*F5^2+8*v1^4*F0*F1*F3-32*v1^3*v0*F0*F2-16*v2^4*F0*F2*F6+4*v1^4*F1^2*F2-16*v1^4*F0^2*F4-16*v1^4*F0*F2^2+8*v1^3*v0*F1^2-12*v1^2*v0^2*F0+4*v2^4*F1^2*F6+4*v3^4*F3^2*F6-16*v3^4*F0*F6^2+4*v0^2*v3^2*F4-8*v2^3*v0*F0*F5+4*v1^3*v2*F1^2*F3+4*v1^2*v2^2*F1^2*F4+4*v1*v2^3*F1^2*F5-32*v1^3*v2*F0^2*F5-48*v1^2*v2^2*F0^2*F6-4*v1*v2*v0^2*F1-16*v3^4*F2*F4*F6+4*v0*v3^3*F3*F5-16*v0*v3^3*F2*F6+32*v1^3*v3*F0^2*F6-8*v1^3*v3*F0*F3^2-16*v1^2*v3^2*F0*F4^2+16*v1^2*v3^2*F1^2*F6-16*v1*v3^3*F0*F5^2+12*v2^2*v3^2*F0*F5^2+8*v2*v3^3*F1*F5^2-16*v1^3*v2*F0*F2*F3-8*v1^2*v2^2*F0*F1*F5-16*v1^2*v2^2*F0*F2*F4-16*v1*v2^3*F0*F1*F6-16*v1*v2^3*F0*F2*F5-24*v1^2*v2*v0*F0*F3-16*v1*v2^2*v0*F0*F4-16*v1^3*v3*F0*F1*F5-48*v1^2*v3^2*F0*F2*F6+24*v1^2*v3^2*F0*F3*F5-8*v1^2*v3^2*F1*F2*F5+32*v1*v3^3*F0*F4*F6-16*v1*v3^3*F1*F3*F6-4*v1^2*v0*v3*F1*F3-16*v1^2*v0*v3*F0*F4-8*v1*v0*v3^2*F1*F5-32*v2^3*v3*F0*F3*F6-64*v2^2*v3^2*F0*F4*F6-8*v2^2*v3^2*F1*F3*F6-16*v2*v3^3*F0*F5*F6-32*v2*v3^3*F1*F4*F6-4*v2^2*v0*v3*F1*F5-48*v2^2*v0*v3*F0*F6-32*v2*v0*v3^2*F1*F6-4*v1*v2*v3^2*F1*F3*F5-16*v1^2*v2*v3*F0*F1*F6-16*v1^2*v2*v3*F0*F3*F4-8*v1^2*v2*v3*F1^2*F5-24*v1*v2^2*v3*F0*F3*F5-16*v1*v2^2*v3*F1^2*F6-16*v1*v2*v3^2*F0*F4*F5-16*v1*v2*v3^2*F1*F2*F6-24*v1*v2*v0*v3*F0*F5-8*v1*v2*v0*v3*F1*F4;
		if IsPoint( K2, [C3,C2,C1,C0] ) then;
		        KP := K2![C3,C2,C1,C0];
		        TP := RationalPoints( J2, KP )[1];
		        Append( ~Retuple, TP );
		else    K2,[C3,C2,C1,C0]; error "Error: [Bo3IsogMap] Point not on the Kummer";
		end if;
	end for;

	return J2, Retuple;
end function;
