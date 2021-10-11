load "Gen2Lib.m";
load "2RichLib.m";
load "3RichLib.m";
load "Gen2IsogLib.m";

SetColumns(0);

////	Checks is Ker is a rank 2, maximal 2^n-isotropic subgroup
Is_2n2n_Subgroup := function( Ker, n )
        J := Parent(Ker[1]);
        //  Checking number of generators
        if #Ker ne 2 then;                                              return false, 1;        end if;
        //  Checking order of generators
        if (Power(2,n)*Ker[1] ne J!0) then;                             return false, 2;        end if;
        if (Power(2,n)*Ker[2] ne J!0) then;                             return false, 3;        end if;
        if (Power(2,n-1)*Ker[1] eq J!0) then;                           return false, 4;        end if;
        if (Power(2,n-1)*Ker[2] eq J!0) then;                           return false, 5;        end if;
        //  Checking linear independence
        if (Power(2,n-1)*Ker[1] eq Power(2,n-1)*Ker[2]) then;           return false, 6;        end if;
        //  Checking Weil pairing
        if WeilPairing( Ker[1], Ker[2], Power(2,n) ) ne 1 then;         return false, 7;        end if;

        return true;
end function;

////	Checks is Ker is a rank 2, maximal 3^n-isotropic subgroup
Is_3n3n_Subgroup := function( Ker, n )
        J := Parent(Ker[1]);
        //  Checking number of generators
        if #Ker ne 2 then;                                              return false, 1;        end if;
        //  Checking order of generators
        if (Power(3,n)*Ker[1] ne J!0) then;                             return false, 2;        end if;
        if (Power(3,n)*Ker[2] ne J!0) then;                             return false, 3;        end if;
        if (Power(3,n-1)*Ker[1] eq J!0) then;                           return false, 4;        end if;
        if (Power(3,n-1)*Ker[2] eq J!0) then;                           return false, 5;        end if;
        //  Checking linear independence
        if (Power(3,n-1)*Ker[1] eq Power(3,n-1)*Ker[2]) then;           return false, 6;        end if;
        if (Power(3,n-1)*Ker[1] eq 2*Power(3,n-1)*Ker[2]) then;         return false, 7;        end if;
        //  Checking Weil pairing
        if WeilPairing( Ker[1], Ker[2], Power(3,n) ) ne 1 then;         return false, 8;        end if;

        return true;
end function;

////	Chooses secret scalars in the vein of the original FT19 paper
////	Note that this function returns a very simple set of scalars
ChooseSecret := function( TorGens, deg )
        pA := Factorisation( deg )[1,1];
        eA := Factorisation( deg )[1,2];

        e12 := WeilPairing( TorGens[1], TorGens[2], deg );
        e13 := WeilPairing( TorGens[1], TorGens[3], deg );
        e14 := WeilPairing( TorGens[1], TorGens[4], deg );
        e23 := WeilPairing( TorGens[2], TorGens[3], deg );
        e24 := WeilPairing( TorGens[2], TorGens[4], deg );
        e34 := WeilPairing( TorGens[3], TorGens[4], deg );

        a12 := Log( e12, e12 );
        a13 := Log( e12, e13 );
        a14 := Log( e12, e14 );
        a23 := Log( e12, e23 );
        a24 := Log( e12, e24 );
        a34 := Log( e12, e34 );

        repeat          a := [ Random(deg) : ind in [1,2,3] ];
        until           ((a[1] mod pA ne 0) or (a[2] mod pA ne 0)) and (a[3] mod pA ne 0);
        Append( ~a, Solution( a14*a[1]+a24*a[2], -a13*a[1]*a[3]-a23*a[2]*a[3], deg ) );

        return a;
end function;

////	Chooses secret scalars in the vein of the original FT19 paper
////	Able to get 12 scalars.
ChooseMoreSecrets := function( TorGens, deg )
        pA := Factorisation( deg )[1,1];
        eA := Factorisation( deg )[1,2];

        e12 := WeilPairing( TorGens[1], TorGens[2], deg );
        e13 := WeilPairing( TorGens[1], TorGens[3], deg );
        e14 := WeilPairing( TorGens[1], TorGens[4], deg );
        e23 := WeilPairing( TorGens[2], TorGens[3], deg );
        e24 := WeilPairing( TorGens[2], TorGens[4], deg );
        e34 := WeilPairing( TorGens[3], TorGens[4], deg );

        a12 := Log( e12, e12 );
        a13 := Log( e12, e13 );
        a14 := Log( e12, e14 );
        a23 := Log( e12, e23 );
        a24 := Log( e12, e24 );
        a34 := Log( e12, e34 );
	
	repeat		r := [ Random(deg) : ind in [1..4] ];
	until		((r[1] mod pA ne 0) or (r[2] mod pA ne 0)) or (r[3] mod pA ne 0) or (r[4] mod pA ne 0);

        repeat          s := [ Random(deg) : ind in [1,2,3] ];
        until           ((s[1] mod pA ne 0) or (s[2] mod pA ne 0)) or (s[3] mod pA ne 0);

        Append( ~s, Solution( a14*r[1]+a24*r[2]+a34*r[3], -r[1]*s[2]+r[2]*s[1] - a13*(r[1]*s[3]-r[3]*s[1]) - a23*(r[2]*s[3]-r[3]*s[2]) + a14*r[4]*s[1] + a24*r[4]*s[2] + a34*r[4]*s[3], deg ) );
        return r,s;
end function;

////	Defining the oracle that returns the G2-invariants
Oracle := function( Basis, secret, eA )
	Ker := [ &+[ secret[1,ind]*Basis[ind] : ind in [1..4] ], &+[ secret[2,ind]*Basis[ind] : ind in [1..4] ] ];
	return G2Invariants(LongG2Isogeny( Ker, 2^eA ));
end function;

////	Defining the oracle that returns 2 bits, IsIsotropic, and if the guess is correct
////	Note that IsIsotropic can be done by the attacker, so it's not useful information; 
////	it has been included here for debugging purposes.
OracleStrong := function( Basis, secret, eA )
	Ker := [ &+[ secret[1,ind]*Basis[ind] : ind in [1..4] ], &+[ secret[2,ind]*Basis[ind] : ind in [1..4] ] ];
	IsIsotropic := Is_2n2n_Subgroup(Ker,eA);
	if IsIsotropic then
		return IsIsotropic, G2Invariants(LongG2Isogeny( Ker, 2^eA ));
	else
		return IsIsotropic, _;
	end if;
end function;

////	Testing if the Weil pairing countermeasure can detect the adaptive attack
WeilCountermeasure := function( SPts, MalPts, p, eA )
	if not CheckSabrinaGenerators(SPts,p,eA) then;					return false,1;	end if;
	if not CheckSabrinaGenerators(MalPts,p,eA) then;				return false,2;	end if;
	n := Power(p,eA);
	if WeilPairing(SPts[1],SPts[3],n) ne WeilPairing(MalPts[1],MalPts[3],n) then;	return false,3;	end if;
	return true;
end function;

////////////////////////////////////////////////////
////	Adaptive attack functions begin here	////
////////////////////////////////////////////////////

////	Recovery of the first bit is done in this function
AdaptiveAttack_firstbit := function( SPts, secret, eA )

	RefInvs := Oracle(SPts,secret,eA);

	T1 := Power(2,eA-1)*SPts[1];
	T2 := Power(2,eA-1)*SPts[2];
	T3 := Power(2,eA-1)*SPts[3];
	T4 := Power(2,eA-1)*SPts[4];
	
	////	Expressing the transformations as malformed points to be fed into the oracle
	tr0  := [ SPts[1], SPts[2], SPts[3]+T1, SPts[4] ];
	tr2  := [ SPts[1], SPts[2], SPts[3], SPts[4]+T2 ];
	tr4  := [ SPts[1], SPts[2], SPts[3]+T2, SPts[4]+T1 ];
	tr21 := [ SPts[1]+T3, SPts[2], SPts[3], SPts[4]+T2 ];
	tr03 := [ SPts[1], SPts[2]+T4, SPts[3]+T1, SPts[4] ];

	////	Logic tree used as presented in the paper
	LogicTree := [* tr4, tr0, tr21, tr2, tr2, tr03, tr03, 0,1,4,7,2,6,3,5 *];
	ind := 1;

	repeat
		Invs := Oracle(LogicTree[ind],secret,eA);
		ind *:= 2;	
		if Invs ne RefInvs then
			ind +:= 1;
		end if;
	until ind gt 7;

	temp := Intseq(LogicTree[ind],2);
	bits := [ [x] : x in temp ];
	while #bits lt 3 do
		Append(~bits,0);
	end while;
	return Reverse(bits);
end function;

////	The iterative step of the adaptive attack in rank 2
AdaptiveAttack_Iterative := function( SPts, bits, secret, eA )

	RefInvs := Oracle(SPts,secret,eA);

	i := #bits[1];
	Ka := &+[ bits[1,ind]*Power(2,ind-1) : ind in [1..i] ];
	Kb := &+[ bits[2,ind]*Power(2,ind-1) : ind in [1..i] ];
	Kc := &+[ bits[3,ind]*Power(2,ind-1) : ind in [1..i] ];

	T1 := Power(2,eA-i-1)*SPts[1];	R1 := Power(2,eA-i-2)*SPts[1];
	T2 := Power(2,eA-i-1)*SPts[2];	R2 := Power(2,eA-i-2)*SPts[2];
	T3 := Power(2,eA-i-1)*SPts[3];	R3 := Power(2,eA-i-2)*SPts[3];
	T4 := Power(2,eA-i-1)*SPts[4];	R4 := Power(2,eA-i-2)*SPts[4];

	////    Testing if [ai,ci] = [0,0]
	MalPts := [ SPts[1] - R1 - Ka*T3, SPts[2] + R2 + Kc*T4, SPts[3] + R3, SPts[4] - R4 ];
	Invs := Oracle(MalPts,secret,eA);
	if Invs eq RefInvs then
		Append(~bits[1],0);
		Append(~bits[3],0);
	else
      	////    Testing if [ai,ci] = [1,0]
		MalPts := [ SPts[1] - R1 - Ka*T3 - Power(2,eA-1)*SPts[3], SPts[2] + R2 + Kc*T4, SPts[3] + R3, SPts[4] - R4 ];
		Invs := Oracle(MalPts,secret,eA);
		if Invs eq RefInvs then
			Append(~bits[1],1);
			Append(~bits[3],0);
		else
			Append(~bits[3],1);
		end if;
	end if;
	////    Concluded that ci is odd, so now, recovering ai
	if #bits[1] ne #bits[3] then
		MalPts := [ SPts[1] - R1 - Ka*T3, SPts[2] + R2 + Kc*T4-Power(2,eA-1)*SPts[4], SPts[3] + R3, SPts[4] - R4 ];
		Invs := Oracle(MalPts,secret,eA);
		if Invs eq RefInvs then
			Append(~bits[1],0);
		else
			Append(~bits[1],1);
		end if;
	end if;

	////    Recovering bi
	Ka := &+[ bits[1,ind]*Power(2,ind-1) : ind in [1..i+1] ];
	Kc := &+[ bits[3,ind]*Power(2,ind-1) : ind in [1..i+1] ];
	T4 := Power(2,eA-i-1)*SPts[4];
	MalPts := [	SPts[1] - R1 - Ka*T3 - Kb*T4,
			SPts[2] - R2 - Kb*T3 - Kc*T4,
			SPts[3] + R3,
			SPts[4] + R4 ];

	Invs := Oracle(MalPts,secret,eA);
	if Invs eq RefInvs then
		Append(~bits[2],0);
	else
		Append(~bits[2],1);
	end if;

	return bits;
end function;






//////////////////////////////////////////////////////////
//	Setting up the parameters for the cryptosystem	//
//	Note that S_Pts are symplectic			//
//////////////////////////////////////////////////////////
p := 24554940634497023;
eA := 25;
eB := 16;
K<u> := GF(p^2);
R<x>:=PolynomialRing(K);

C0 := HyperellipticCurve( (13274801814165018*K.1 + 7650378754263570)*x^6
                        + (10468506766346375*K.1 + 2679228971360392)*x^5
                        + (21625069997560015*K.1 + 7231499835169234)*x^4
                        + (23300095300354839*K.1 + 20580385459668126)*x^3
                        + (5065415789788622*K.1 + 11531147184110145)*x^2
                        + (23889770567634828*K.1 + 10123228279895739)*x
                        + (7551381872957476*K.1 + 22216347959038604) );
J0 := Jacobian( C0 );

S_Pts := [  J0![ x^2 + (5882126085128680*u + 5094819132888242)*x + 22605189563423706*u + 16582211147969147,
                + (565139765053753*u + 6333816027130590)*x + 11119083842128041*u + 2038564411848191 ],
              J0![ x^2 + (6289897457713628*u + 122793681401835)*x + 8159987670043790*u + 8921765588125874,
                + (6797171283604390*u + 8027782075686861)*x + 6499694411024956*u + 998188348471942 ],
              J0![ x^2 + (11262646108815318*u + 11387072088286839)*x + 22158795934302818*u + 7393997097768434,
                + (1499581526062332*u + 13898905591994626)*x + 7581790876278230*u + 12625297707942236 ],
              J0![ x^2 + (4339080709336339*u + 17690009128448464)*x + 19473379694810982*u + 8109073875542836,
                + (20819284304914568*u + 7273533053870089)*x + 10325771246498769*u + 19655488592111745 ] ];


///////////////////////////////////////////////////
//  This is the rank 2 sympletic implementation  //
///////////////////////////////////////////////////
Alice_a := 25067790;
Alice_b := 4812782;
Alice_c := 6567741;
r := [ 1, 0, Alice_a, Alice_b ];
s := [ 0, 1, Alice_b, Alice_c ];
Q1 := &+[ r[ind]*S_Pts[ind] : ind in [1..4] ];
Q2 := &+[ s[ind]*S_Pts[ind] : ind in [1..4] ];

print "Recovered:";
AdaptiveAttack_firstbit( S_Pts, [r,s], eA );
print bits;
  
////	We have to brute force the last two bits, so the code stops at eA-2
for ind in [2..eA-2] do
	bits := AdaptiveAttack_Iterative( S_Pts, bits, [r,s], eA );
	print bits;
end for;

print "Reference:";
print Intseq(Alice_a,2);
print Intseq(Alice_b,2);
print Intseq(Alice_c,2);


