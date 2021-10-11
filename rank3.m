load "Gen2Lib.m";
load "2RichLib.m";
load "3RichLib.m";
load "Gen2IsogLib.m";

SetColumns(0);

//Is_2n2n_Subgroup := function( Ker, n )
//        J := Parent(Ker[1]);
//        //  Checking number of generators
//        if #Ker ne 2 then;                                              return false, 1;        end if;
//        //  Checking order of generators
//        if (Power(2,n)*Ker[1] ne J!0) then;                             return false, 2;        end if;
//        if (Power(2,n)*Ker[2] ne J!0) then;                             return false, 3;        end if;
//        if (Power(2,n-1)*Ker[1] eq J!0) then;                           return false, 4;        end if;
//        if (Power(2,n-1)*Ker[2] eq J!0) then;                           return false, 5;        end if;
//        //  Checking linear independence
//        if (Power(2,n-1)*Ker[1] eq Power(2,n-1)*Ker[2]) then;           return false, 6;        end if;
//        //  Checking Weil pairing
//        if WeilPairing( Ker[1], Ker[2], Power(2,n) ) ne 1 then;         return false, 7;        end if;
//
//        return true, _;
//end function;
//
//Is_Rank3_Subgroup := function( Ker,gpstruct )
//	J := Parent(Ker[1]);
//	n := gpstruct[1];
//	a := gpstruct[2];
//	b := gpstruct[3];
//        //  Checking group structure
//        if #Ker ne 3 then;                                              return false, [1,1];	end if;
//	if n ne gpstruct[1] then;					return false, [1,2];	end if;
//	if n ne (a+b) then;						return false, [1,3];	end if;
//        //  Checking order of generators
//        if (Power(2,n)*Ker[1] ne J!0) then;                             return false, [2,1];	end if;
//        if (Power(2,a)*Ker[2] ne J!0) then;                             return false, [2,2];	end if;
//        if (Power(2,b)*Ker[3] ne J!0) then;                             return false, [2,3];    end if;
//        if (Power(2,n-1)*Ker[1] eq J!0) then;                           return false, [3,1];	end if;
//        if (Power(2,a-1)*Ker[2] eq J!0) then;                           return false, [3,2];	end if;
//        if (Power(2,b-1)*Ker[3] eq J!0) then;                           return false, [3,3];	end if;
//        //  Checking linear independence
//        if (Power(2,n-1)*Ker[1] eq Power(2,a-1)*Ker[2]) then;           return false, [4,12];	end if;
//        if (Power(2,n-1)*Ker[1] eq Power(2,b-1)*Ker[3]) then;           return false, [4,13];	end if;
//        if (Power(2,a-1)*Ker[2] eq Power(2,b-1)*Ker[3]) then;           return false, [4,23];	end if;
//        //  Checking Weil pairing
//        if WeilPairing( Ker[1], Ker[2], Power(2,n) ) ne 1 then;         return false, [5,12];        end if;
//        if WeilPairing( Ker[1], Ker[3], Power(2,n) ) ne 1 then;         return false, [5,13];        end if;
//
//        return true,_;
//
//end function;

////	This function chooses secrets for rank 3 for a given k.
ChooseSecretRank3 := function( p, eA, k )
	if k eq 0 then;
		a := Random(Power(p,eA));
		b := Random(Power(p,eA));
		c := Random(Power(p,eA));
		return [a,b,c];
	elif 2*k le eA then;
		a := Random(Power(p,eA));
		b := Random(Power(p,eA-k));
		c := Random(Power(p,eA-2*k));
		d := Random(Power(p,k));
		return [a,b,c,d];
	else
		error "Error: Invalid k.";
	end if;
end function;

////	This is the oracle for rank 3. It outputs 2 bits of information,
////	but like the rank 2 oracle, the IsIsotropic flag is for internal
////	use only.
OracleRank3 := function( Basis, secret, gpstruct )
	eA := gpstruct[1];
	Q1 := &+[ secret[1,ind]*Basis[ind] : ind in [1..4] ];
	Q2 := &+[ secret[2,ind]*Basis[ind] : ind in [1..4] ];
	Q3 := &+[ secret[3,ind]*Basis[ind] : ind in [1..4] ];
	Ker := [ Q1,Q2,Q3 ];
	IsIsotropic,reason := Is_Rank3_Subgroup(Ker,gpstruct);
	if IsIsotropic then
		return IsIsotropic, G2Invariants(LongRank3G2Isogeny( Ker, 2^eA, gpstruct ));
	else
		return IsIsotropic, reason;
	end if;
end function;


////	First bit for k=1, rank 3 case.
AdaptiveAttack_Rank3_FirstStep := function( SPts, secret, gpstruct )
	_, RefInvs := OracleRank3(SPts,secret,gpstruct);
	eA := gpstruct[1];
	bits := [[],[],[],[]];

	T1 := Power(2,eA-1)*SPts[1];
	T2 := Power(2,eA-1)*SPts[2];
	T4 := Power(2,eA-1)*SPts[4];
	MalPts := [	[ SPts[1], SPts[2], SPts[3]+T1, SPts[4] ], 
			[ SPts[1], SPts[2], SPts[3], SPts[4]+T2 ],
			[ SPts[1], SPts[2]+T4, SPts[3], SPts[4] ]];
	candies := [ 1,2,4 ];

	for ind in [1..3] do
		IsIsotropic, Invs := OracleRank3(MalPts[ind],secret,gpstruct);
		if IsIsotropic then
			if Invs eq RefInvs then
				Append(~bits[candies[ind]],0);
			else
				Append(~bits[candies[ind]],1);
			end if;
		else
			print Invs;
		end if;
	end for;
	return bits;
end function;

////	I have three implementations of recovering a and c.
////	This is because of the complexity of handling many different group
////	structures. For general purposes use V3 which requires that you provide
////	b in full. This is at odds with the paper, but this code aims to just
////	be a proof-of-concept only.
Recover_a_c := function( gpstruct, S_Pts, recoveredsecrets, secret, RefInvs )
	eA,_,k := Explode(gpstruct);
	a,_,c,d := Explode(recoveredsecrets);
	abits := [ a ];
	cbits := [ c ];
	ac_candy := [ [0,0],[1,0],[0,1],[1,1] ];
	R := IntegerRing(2^eA);

	for ind in [1..eA] do
		a := PListToDec(abits,2);
		c := PListToDec(cbits,2);

		l := eA-ind-1;
		T := R!(1-2^(l));
		invT := Integers()!(1/T);
		theta := SquareRoot(T);
		invtheta := Integers()!(1/theta);
		theta := Integers()!theta;

		T1 := IntegerRing()!(R!(2^(l-1))/R!(1-2^(l)));
		T2 := IntegerRing()!(R!(2^l)/R!(1-2^l));

		alpha := [ -2^(l)*(a-2^(l-2)*invT*c*d^2), 	  -2^(l)*((a+2^ind)-2^(l-2)*invT*c*d^2),
			   -2^(l)*(a-2^(l-2)*invT*(c+2^ind)*d^2), -2^(l)*((a+2^ind)-2^(l-2)*invT*(c+2^ind)*d^2) ];
		beta  := [ -T1*c*d, -T1*c*d, -T1*(c+2^ind)*d, -T1*(c+2^ind)*d ];
		gamma := [ -T2*c, -T2*c, -T2*(c+2^ind), -T2*(c+2^ind) ];
		delta := -2^(l-1)*invT *d;
		for jnd in [1..4] do
			MalPts := [ theta*S_Pts[1] + delta*theta*S_Pts[2] + (invtheta*alpha[jnd]-beta[jnd]*delta*theta)*S_Pts[3] + beta[jnd]*theta*S_Pts[4],
				    invtheta*S_Pts[2] + (invtheta*beta[jnd]+theta*gamma[jnd]*delta)*S_Pts[3] - theta*gamma[jnd]*S_Pts[4],
			      	    invtheta*S_Pts[3],
				    -theta*delta*S_Pts[3] + theta*S_Pts[4] ];
			IsSymplectic, Invs := OracleRank3(MalPts,secret,gpstruct);
			if IsSymplectic then
				if Invs eq RefInvs then
					Append(~abits,ac_candy[jnd,1]);
					Append(~cbits,ac_candy[jnd,2]);
					break;
				end if;
			else
				print "Not symplectic";
			end if;
		end for;
		abits;
		cbits;
	end for;
	return PListToDec(abits,2),PListToDec(cbits,2);
end function;

Recover_a_c_V2 := function( gpstruct, S_Pts, recoveredsecrets, secret, RefInvs )
	eA,_,k := Explode(gpstruct);
	a,_,c,d := Explode(recoveredsecrets);
	abits := [ a ];
	cbits := [ c ];
	ac_candy := [ [0,0],[1,0],[0,1],[1,1] ];
	R := IntegerRing(2^eA);

	for ind in [1..k-1] do
		a := PListToDec(abits,2);
		c := PListToDec(cbits,2);

		l := eA-ind-1;
		T := R!(1-2^l);
		invT := Integers()!(1/T);
		theta := SquareRoot(T);
		invtheta := Integers()!(1/theta);
		theta := Integers()!theta;
		T := Integers()!T;

		alpha := [ -2^l*invT*a, -2^l*invT*(a+2^ind) ];
		beta  :=   -2^(l-1)*invT*d*c;
		gamma :=    2^l*c;
		delta :=   -2^(l-1)*invT *d;
		for jnd in [1,2] do
			MalPts := [ 	   theta*( S_Pts[1] + delta*S_Pts[2] + alpha[jnd]*S_Pts[3] + beta*S_Pts[4] ),
					invtheta*( S_Pts[2] + T*beta*S_Pts[3] + gamma*S_Pts[4] ),
					invtheta*( S_Pts[3] ),
					   theta*( -delta*S_Pts[3] + S_Pts[4] ) ];
			IsSymplectic, Invs := OracleRank3(MalPts,secret,gpstruct);
			if IsSymplectic then
				if Invs eq RefInvs then
					Append(~abits,jnd-1);
					break;
				end if;
			else
				print "Not symplectic";
			end if;
		end for;
		abits;
		cbits;

	end for;

	for ind in [Max(1,k)..eA] do
		a := PListToDec(abits,2);
		c := PListToDec(cbits,2);

		l := eA-ind-1;
		T := R!(1-2^l);
		invT := Integers()!(1/T);
		theta := SquareRoot(T);
		invtheta := Integers()!(1/theta);
		theta := Integers()!theta;
		T := Integers()!T;

		alpha := [ -2^l*invT*a, -2^l*invT*(a+2^ind) ];
		beta  := [ -2^(l-1)*invT*d*c, -2^(l-1)*invT*d*(c+2^(ind-k+1)) ];
		gamma := [  2^l*c, 2^l*(c+2^(ind-k+1)) ];
		delta :=   -2^(l-1)*invT *d;
		for jnd in [1,2] do
		for knd in [1,2] do
			MalPts := [ 	   theta*( S_Pts[1] + delta*S_Pts[2] + alpha[jnd]*S_Pts[3] + beta[knd]*S_Pts[4] ),
					invtheta*( S_Pts[2] + T*beta[knd]*S_Pts[3] + gamma[knd]*S_Pts[4] ),
					invtheta*( S_Pts[3] ),
					   theta*( -delta*S_Pts[3] + S_Pts[4] ) ];
			IsSymplectic, Invs := OracleRank3(MalPts,secret,gpstruct);
			if IsSymplectic then
				if Invs eq RefInvs then
					Append(~abits,jnd-1);
					Append(~cbits,knd-1);
					break;
				end if;
			else
				print "Not symplectic";
			end if;
		end for;
		end for;
		abits;
		cbits;
	end for;
	return PListToDec(abits,2),PListToDec(cbits,2);
end function;


Recover_a_c_V3 := function( gpstruct, S_Pts, recoveredsecrets, secret, RefInvs )
	eA,_,k := Explode(gpstruct);
	a,b,c,d := Explode(recoveredsecrets);
	abits := [ a ];
	cbits := [ c ];
	R := IntegerRing(2^eA);

	for ind in [1..k-1] do
		a := PListToDec(abits,2);
		c := PListToDec(cbits,2);

		l := eA-ind-1;
		T := R!(1-2^l);
		invT := Integers()!(1/T);
		theta := SquareRoot(T);
		invtheta := Integers()!(1/theta);
		theta := Integers()!theta;
		T := Integers()!T;

		alpha := [ -2^l*invT*a, -2^l*invT*(a+2^ind) ];
		beta  :=   -2^(l-1)*invT*d*c;
		gamma :=    2^l*c;
		delta :=   -2^(l-1)*invT *d;
		for jnd in [1,2] do
			MalPts := [ 	   theta*( S_Pts[1] + delta*S_Pts[2] + alpha[jnd]*S_Pts[3] + beta*S_Pts[4] ),
					invtheta*( S_Pts[2] + T*beta*S_Pts[3] + gamma*S_Pts[4] ),
					invtheta*( S_Pts[3] ),
					   theta*( -delta*S_Pts[3] + S_Pts[4] ) ];
			IsSymplectic, Invs := OracleRank3(MalPts,secret,gpstruct);
			if IsSymplectic then
				if Invs eq RefInvs then
					Append(~abits,jnd-1);
					break;
				end if;
			else
				print "Not symplectic";
			end if;
		end for;
		abits;
	end for;

	for ind in [Max(1,k)..eA-k-2] do
		a := PListToDec(abits,2);
		c := PListToDec(cbits,2);

		l := eA-ind-1;
		T := R!(1-2^l);
		invT := Integers()!(1/T);
		theta := SquareRoot(T);
		invtheta := Integers()!(1/theta);
		theta := Integers()!theta;
		T := Integers()!T;

		alpha := [ -2^l*invT*a, -2^l*invT*(a+2^ind) ];
		beta  := [ -2^(l-1)*invT*d*c, -2^(l-1)*invT*d*(c+2^(ind-k+1)) ];
		gamma := [  2^l*c, 2^l*(c+2^(ind-k+1)) ];
		delta :=   -2^(l-1)*invT *d;
		for jnd in [1,2] do
		for knd in [1,2] do
			MalPts := [ 	   theta*( S_Pts[1] + delta*S_Pts[2] + alpha[jnd]*S_Pts[3] + beta[knd]*S_Pts[4] ),
					invtheta*( S_Pts[2] + T*beta[knd]*S_Pts[3] + gamma[knd]*S_Pts[4] ),
					invtheta*( S_Pts[3] ),
					   theta*( -delta*S_Pts[3] + S_Pts[4] ) ];
			IsSymplectic, Invs := OracleRank3(MalPts,secret,gpstruct);
			if IsSymplectic then
				if Invs eq RefInvs then
					Append(~abits,jnd-1);
					Append(~cbits,knd-1);
					break;
				end if;
			else
				print "Not symplectic";
			end if;
		end for;
		end for;
		abits;
		cbits;
	end for;

	for ind in [Max(1,eA-k-1)..eA] do
		a := PListToDec(abits,2);
		c := PListToDec(cbits,2);

		l := eA-ind-1;
		T := R!(1-2^l);
		invT := Integers()!(1/T);
		theta := SquareRoot(T);
		invtheta := Integers()!(1/theta);
		theta := Integers()!theta;
		T := Integers()!T;
		
		alpha := [ 2^l*(a+b*d-invT*c*d^2), 2^l*((a+2^ind)+b*d-invT*c*d^2) ];
		beta  := 2^l*invT*c*d;
		gamma := 2^l*invT*c;
		delta := 2^l*d;
		for jnd in [1,2] do
			MalPts := [ 	invtheta*( S_Pts[1] + delta*S_Pts[2] + (alpha[jnd]+beta*delta)*S_Pts[3] + (beta-gamma*delta)*S_Pts[4] ),
					   theta*( S_Pts[2] + beta*S_Pts[3] - gamma*S_Pts[4] ),
					   theta*( S_Pts[3] ),
					invtheta*( -delta*S_Pts[3] + S_Pts[4] ) ];
			IsSymplectic, Invs := OracleRank3(MalPts,secret,gpstruct);
			if IsSymplectic then
				if Invs eq RefInvs then
					Append(~abits,jnd-1);
					break;
				end if;
			else
				print "Not symplectic";
			end if;
		end for;
		abits;
	end for;

	return PListToDec(abits,2),PListToDec(cbits,2);
end function;

////	This is the p-adic evaluation of N.
////	This is used in the next function.
myval := function( N, p )
	ind := 0;
	while (N mod p) eq 0 do
		N := ExactQuotient(N,p);
		ind +:= 1;
	end while;
	return ind;
end function;

////	Recovering b after a and c are known.
////	Again, this is in contrary with the paper, but in most cases
////	a and c have been recovered full. Again, this is just to 
////	prove that the concept we have here works.
Recovering_b := function( gpstruct, S_Pts, K, secret, RefInvs )
	eA,_,k := Explode(gpstruct);
	a,b,c,d := Explode(K);
	bbits := [ b ];

	for ind in [1+myval(d,2)..eA-k] do 

		b := PListToDec(bbits,2);

		l := eA-ind-1;
		T := IntegerRing(2^eA)!(1-2^l);
		invT := Integers()!(1/T);
		theta := SquareRoot(T);
		invtheta := Integers()!(1/theta);
		theta := Integers()!theta;
	
		alpha := 2^l*(a+b*d-c*d^2);
		beta  := 2^l*c*d;
		gamma := 2^l*invT*c;
		delta := 2^l*d;

		MalPts := [ invtheta*(S_Pts[1] + delta*S_Pts[2] + alpha*S_Pts[3] + beta*S_Pts[4]),
			    theta*(S_Pts[2] + beta*invtheta*S_Pts[3] - gamma*S_Pts[4]),
			    theta*S_Pts[3],
			    invtheta*(-delta*S_Pts[3] + S_Pts[4]) ];
		_, Invs := OracleRank3(MalPts,secret,[eA,eA-k,k]);
		if Invs eq RefInvs then
			Append(~bbits,0);
		else
			Append(~bbits,1);
		end if;
		bbits;
	end for;
	return PListToDec(bbits,2);
end function;



////////////////////////////////////////////
////	Setting up the cryptosystem	////
////////////////////////////////////////////
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

////	These are symplectic basis points for Alice.
S_Pts := [    J0![ x^2 + (5882126085128680*u + 5094819132888242)*x + 22605189563423706*u + 16582211147969147,
                + (565139765053753*u + 6333816027130590)*x + 11119083842128041*u + 2038564411848191 ],
              J0![ x^2 + (6289897457713628*u + 122793681401835)*x + 8159987670043790*u + 8921765588125874,
                + (6797171283604390*u + 8027782075686861)*x + 6499694411024956*u + 998188348471942 ],
              J0![ x^2 + (11262646108815318*u + 11387072088286839)*x + 22158795934302818*u + 7393997097768434,
                + (1499581526062332*u + 13898905591994626)*x + 7581790876278230*u + 12625297707942236 ],
              J0![ x^2 + (4339080709336339*u + 17690009128448464)*x + 19473379694810982*u + 8109073875542836,
                + (20819284304914568*u + 7273533053870089)*x + 10325771246498769*u + 19655488592111745 ] ];


///////////////////////////////////////////////////
//  This is the rank 3 sympletic implementation  //
///////////////////////////////////////////////////
////	Alice's secrets; k=1
//k := 1;
//Alice_a := 25843517;
//Alice_b := 7012151;
//Alice_c := 2632946;
//Alice_d := 1;

////	Alice's secrets; k=2
//k := 2;
//Alice_a := 25843517;
//Alice_b := 1756127;
//Alice_c := 545095;
//Alice_d := 1;

k := 10;
Alice_a := 24389460;
Alice_b := 18168;
Alice_c := 25;
Alice_d := 955;


////	Alice's secrets expressed as linear combinations of the basis.
r := [ 1, Alice_d, Alice_a, Alice_b ];
s := [ 0, 2^k, 2^k*(Alice_b-Alice_d*Alice_c), 2^k*Alice_c ];
t := [ 0, 0, -2^(eA-k)*Alice_d, 2^(eA-k) ];
_, RefInvs := OracleRank3(S_Pts,[r,s,t],[eA,eA-k,k]);



AdaptiveAttack_Rank3_FirstStep( S_Pts, [r,s,t], [eA,eA-k,k] );

Intseq(Alice_a,2);
Intseq(Alice_c,2);
Recover_a_c_V3 ( [eA,eA-k,k], S_Pts, [a,Alice_b,c,Alice_d], [r,s,t], RefInvs );

Intseq(Alice_b,2);
Recovering_b ( [eA,eA-k,k], S_Pts, [Alice_a,b,Alice_c,Alice_d], [r,s,t], RefInvs );
