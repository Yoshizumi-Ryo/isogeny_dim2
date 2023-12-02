//==============================================
//start of torsion_attack6.m


//auxi. functions.----------------------------



//compute all x s.t. x^2=-1 (mod M), (0<x<M).
function all_4throot_mod(M)
  "Wait for calculating to get prime divisors of M=",M;
  seq_pr_div_M:=PrimeDivisors(M);
  "calculated.";
  prime_factor:=Seqset(seq_pr_div_M);
  assert(M ge 2);
  if not forall{pr:pr in (prime_factor diff {2})|pr mod 4 eq 1} then
    return {};
  end if;
  if IsDivisibleBy(M,4) then
    return {};
  end if;
  fac_M:=Factorization(M);
  CRT_M:=[];
  for i in {1..#fac_M} do
    CRT_M[i]:=fac_M[i][1]^fac_M[i][2];
  end for;
  X_M:=[];
  for i in {1..#fac_M} do
    X_M[i]:=Modsqrt(-1,CRT_M[i]);
    assert(IsDivisibleBy(X_M[i]^2+1,CRT_M[i]));
  end for;
  set_all_4throot_modM:={};
  for bit in CartesianPower({1,-1},#fac_M) do
    Y_M:=[];
    for i in {1..#fac_M} do
      Y_M[i]:=(bit[i]*X_M[i]) mod CRT_M[i];
      assert(IsDivisibleBy(Y_M[i]^2+1,CRT_M[i]));
    end for;
    set_all_4throot_modM join:={CRT(Y_M,CRT_M)};
  end for;
  return set_all_4throot_modM;
end function;


//全探索.
function all_4throot_mod_2(M)
  set:={};
  for r in {1..M} do
    if IsDivisibleBy(r^2+1,M) then
      set join:={r};
    end if;
  end for;
  return set;
end function;



//for given M, we find x,y s.t.x^2+y^2=M and GCD(x,y)=1.
function primitive_Cornacchia(M)
  if M eq 0 then
    return true,0,0;
  elif M eq 1 then
    return true,1,0;
  elif M eq 2 then
    return true,1,1;
  end if;
  assert(M ge 2);
  if #all_4throot_mod(M) ne 0 then
    set_all_4throot_modM:=all_4throot_mod(M);
    for r0 in set_all_4throot_modM do
      if 2*r0 le M then
        r_0:=r0;
        assert((r_0^2+1) mod M eq 0);
        rr:=[];
        r_1:=(M mod r_0);
        while r_1^2 ge M do
          r_2:=r_0 mod r_1;
          r_0:=r_1;
          r_1:=r_2;
        end while;
        assert(r_1^2 lt M);
        if IsSquare(M-r_1^2) then
          _,s:=IsSquare(M-r_1^2);
          assert(r_1^2+s^2 eq M);
          assert(GCD(r_1,s) eq 1);
          return true,r_1,s;
        end if;
      end if;
    end for;
  end if;
  return false;
end function;



//for given M, we find x,y s.t.x^2+y^2=M.
function Cornacchia(M)
  if M eq 0 then
    return true,0,0;
  elif M eq 1 then
    return true,1,0;
  end if;
  assert(M ge 2);
  if primitive_Cornacchia(M) then
    "CC2";
    _,x,y:=primitive_Cornacchia(M);
    assert(x^2+y^2 eq M);
    return true,x,y;
  end if;
  for m in Divisors(M) do
    if IsSquare(m) then
      if primitive_Cornacchia(M div m) then
        _,x,y:=primitive_Cornacchia(M div m);
        _,sqrt_m:=IsSquare(m);
        assert((sqrt_m*x)^2+(sqrt_m*y)^2 eq M);
        return true,sqrt_m*x,sqrt_m*y;
      end if;
    end if;
  end for;
  return false;
end function;



//全探索.
function Cornacchia_2(M)
  if M eq 0 then
    return true,0,0;
  end if;
  for x in {1..(Isqrt(M)+1)} do
    ysq:=M-x^2;
    if IsSquare(ysq) then
      _,y:=IsSquare(ysq);
      return true,x,y; //x^2+y^2=M.
    end if;
  end for;
  return false;
end function;




//get endmorphism of deg=M written by quaternion element.
function FullRepInt_2(C,p)
  assert(C gt p);
  assert(p mod 4 eq 3);
  for i in {1..50000} do
    cd:=Floor(Sqrt(4*C/p));  //m'
    zd:=Random({-cd..cd});   //z'
    cdd:=Floor(Sqrt((4*C/p)-zd^2)); //m"
    td:=Random({-cdd..cdd});  //t'
    c:=4*C-p*(zd^2+td^2);  //M'
    if Cornacchia(c) then
      _,xd,yd:=Cornacchia(c);
      assert(xd^2+yd^2 eq c);
      if ((xd-td) mod 2 eq 0) and ((yd-zd) mod 2 eq 0) then
        x:=((xd-td) div 2);
        y:=((yd-zd) div 2);
        z:=zd;
        t:=td;
        deg:=((xd^2+yd^2+p*(zd^2+td^2)) div 4);
        assert(deg eq C);
        return [x,y,z,t]; //x+y*i+z*((i+j)/2)+t*((1+k)/2).
      end if;
    end if;
  end for;
  "we cannot find.";
  assert(false);
end function;





//return image of d-torsion basis for given rep_normal_basis.
function image_by_repint_2(E,rep_int,P,Q,end_i)
  p:=Characteristic(BaseField(E));
  _<x>:=PolynomialRing(GF(p^4));
  Em_4:=EllipticCurve(x^3-x);
  Ep_4:=EllipticCurve(x^3+x);
  assert(E eq Em_4);
  _,iso_mp:=IsIsomorphic(Em_4,Ep_4);
  iso_pm:=Inverse(iso_mp);
  Pp:=iso_mp(P);
  Qp:=iso_mp(Q);
  assert(end_i^2 eq NegationMap(Ep_4));  //-1=i^2.
  //end_j:=FrobeniusMap(Ep_4);
  end_j:=map<Ep_4->Ep_4| pt :-> [pt[1]^p,pt[2]^p,pt[3]^p]>;
  end_k:=end_i*end_j;
  assert(#{end_i(R)+end_j(R):R in Points(TorsionSubgroupScheme(Ep_4,2))} eq 1);
  x:=rep_int[1];
  y:=rep_int[2];
  z:=rep_int[3];
  t:=rep_int[4];
  //x+y*i+z*((i+j)/2)+t*((1+k)/2).
  if (IsOdd(Order(Pp))) and (IsOdd(Order(Qp))) then
    //end_i;
    //"this",end_i^4;
    //NegationMap(Ep_4);
    Od:=Order(Pp);
    ZmodOd:=quo<IntegerRing()|Od>;
    two_modOd:=ZmodOd!2;
    assert(GCD(2,two_modOd) eq 1);
    inv_twomodOd:=two_modOd^(-1);
    inv_two:=IntegerRing()!inv_twomodOd;
    assert(((inv_two*2) mod Od)eq 1);
    hPp:=inv_two*Pp; //P/N_B.
    hQp:=inv_two*Qp; //Q/N_B.

    //hPp;
    //end_j(hPp);
    //-end_i(hPp);
    //-hPp;
  else
    //"No!";
    hPp:=Pp/2;
    hQp:=Qp/2;
  end if;
  assert(hPp*2 eq Pp);
  assert(hQp*2 eq Qp);

  termP_3:=(end_i(hPp)+end_j(hPp));
  termP_4:=(hPp+end_k(hPp));
  termQ_3:=(end_i(hQp)+end_j(hQp));
  termQ_4:=(hQp+end_k(hQp));
  assert(IsDivisibleBy(Order(Pp),Order(termP_3)));
  assert(IsDivisibleBy(Order(Pp),Order(termP_4)));
  assert(IsDivisibleBy(Order(Qp),Order(termQ_3)));
  assert(IsDivisibleBy(Order(Qp),Order(termQ_4)));
  img_Pp:=x*Pp+y*end_i(Pp)+z*termP_3+t*termP_4;
  img_Qp:=x*Qp+y*end_i(Qp)+z*termQ_3+t*termQ_4;
  assert(IsDivisibleBy(Order(Pp),Order(img_Pp)));
  assert(IsDivisibleBy(Order(Qp),Order(img_Qp)));
  img_Pm:=iso_pm(img_Pp);
  img_Qm:=iso_pm(img_Qp);
  return img_Pm,img_Qm;
end function;



function ellpt_division(P,N)
  fact:=fatoriztion_seq(N);
  for i in {1..#fact} do
    P:=P/fact[i];
  end for;
  return P;
end function;





//P,Q are basis of E[N_A].
//only a*N_B>p.
function construct_auxiliary_img_5(E,N_A,N_B,P,Q)
  assert(Order(P)eq N_A);
  assert(Order(Q)eq N_A);
  p:=Characteristic(BaseField(E));
  _<x>:=PolynomialRing(GF(p^4));
  Em_4:=EllipticCurve(x^3-x);
  assert(E eq Em_4);
  assert(Scheme(P) eq Em_4);
  assert(Scheme(Q) eq Em_4);
  assert(N_A gt N_B);
  a:=N_A-N_B;

  ZmodN_A:=quo<IntegerRing()|N_A>;
  modN_B:=ZmodN_A!N_B;
  assert(GCD(N_A,N_B) eq 1);
  inv_modN_B:=modN_B^(-1);
  inv_N_B:=IntegerRing()!inv_modN_B;
  assert(((N_B*inv_N_B) mod N_A)eq 1);
  PdivNB:=inv_N_B*P; //P/N_B.
  QdivNB:=inv_N_B*Q; //Q/N_B.
  assert(N_B*PdivNB eq P);
  assert(N_B*QdivNB eq Q);
  assert(Order(P) eq N_A);
  assert(Order(Q) eq N_A);
  assert(Order(PdivNB) eq N_A);
  assert(Order(QdivNB) eq N_A);
  assert(a*N_B gt p);

  _<x>:=PolynomialRing(GF(p^4));
  E_p_4:=EllipticCurve(x^3+x);
  end_i:=Automorphisms(E_p_4)[2];
  assert(end_i^2 eq NegationMap(E_p_4));

  for count in {1..30} do
    gamma_repint:=FullRepInt_2(a*N_B,p);
    gamma_PdivNB,gamma_QdivNB:=image_by_repint_2(E,gamma_repint,PdivNB,QdivNB,end_i);
    assert(Scheme(gamma_PdivNB) eq E);
    assert(Scheme(gamma_QdivNB) eq E);
    assert(Order(gamma_PdivNB) eq N_A);
    assert(Order(gamma_QdivNB) eq N_A);
    //"gamma(P/N_B)",gamma_PdivNB;

    //construct basis of ker(dual_delta).------
    S_1,S_2:=ell_to_torsion_basis_2(E,N_B); 
    assert(Order(S_1) eq N_B);
    assert(Order(S_2) eq N_B);
    //basis of ker(dual delta).
    bkdd_1,bkdd_2:=image_by_repint_2(E,gamma_repint,S_1,S_2,end_i);

    if Order(bkdd_1) eq N_B then
      bkdd:=bkdd_1;
      break count;
    elif Order(bkdd_2) eq N_B then
      bkdd:=bkdd_2;
      break count;
    end if;
    if count eq 30 then
      assert(false);
    end if;
  end for;
  assert(Order(bkdd) eq N_B);
  
  Ecd,alpha_P,alpha_Q:=elliptic_isogeny_1ptker(E,bkdd,gamma_PdivNB,gamma_QdivNB);
  assert(Order(P) eq Order(alpha_P));
  assert(Order(Q) eq Order(alpha_Q));
  return Ecd,alpha_P,alpha_Q;
end function;




//P,Q are basis of E[N_A].
//not to only a*N_B>p.
function construct_auxiliary_img_6(E,N_A,N_B,P,Q)
  assert(Order(P)eq N_A);
  assert(Order(Q)eq N_A);
  p:=Characteristic(BaseField(E));
  _<x>:=PolynomialRing(GF(p^4));
  Em_4:=EllipticCurve(x^3-x);
  assert(E eq Em_4);
  assert(Scheme(P) eq Em_4);
  assert(Scheme(Q) eq Em_4);
  assert(N_A gt N_B);
  a:=N_A-N_B;
  ZmodN_A:=quo<IntegerRing()|N_A>;
  modN_B:=ZmodN_A!N_B;
  assert(GCD(N_A,N_B) eq 1);
  inv_modN_B:=modN_B^(-1);
  inv_N_B:=IntegerRing()!inv_modN_B;
  assert(((N_B*inv_N_B) mod N_A)eq 1);
  PdivNB:=inv_N_B*P; //P/N_B.
  QdivNB:=inv_N_B*Q; //Q/N_B.
  assert(N_B*PdivNB eq P);
  assert(N_B*QdivNB eq Q);
  assert(Order(P) eq N_A);
  assert(Order(Q) eq N_A);
  assert(Order(PdivNB) eq N_A);
  assert(Order(QdivNB) eq N_A);
  //assert(a*N_B gt p);

  b:=1;
  if (a*N_B lt p) then //if a*N_B<p, we find b s.t. b*a*N_B>p.
    if IsDivisibleBy(p+1,N_B) then
      ppm:=p+1;
    else
      ppm:=p-1;
    end if;
    assert(IsDivisibleBy(ppm,N_B));

    for NN_B in Divisors(ppm) do
      if (p lt a*NN_B) and IsDivisibleBy(NN_B,N_B) then
        bb:=NN_B div N_B;
        if GCD(N_A,bb) eq 1 and  GCD(a,bb) eq 1 then
          if  (bb*a*N_B gt p) then
            b:=bb;
            "we multply in aux path const.",b,"(In this case, we will make false)";
          end if;
          break NN_B;
        end if;
      end if;
    end for;
  end if;
  if b*a*N_B lt p then
    "There is not appropriate b.";
    assert(false);
  end if;

  assert(b*a*N_B gt p);
  assert(GCD(a,b*N_B) eq 1);
  assert(GCD(N_A,b*N_B) eq 1);
  //assert(N_A gt b*N_B);
  _<x>:=PolynomialRing(GF(p^4));
  E_p_4:=EllipticCurve(x^3+x);
  end_i:=Automorphisms(E_p_4)[2];
  assert(end_i^2 eq NegationMap(E_p_4));

  for count in {1..30} do
    "C1";
    gamma_repint:=FullRepInt_2(b*a*N_B,p);
    "C2";
    gamma_PdivNB,gamma_QdivNB:=image_by_repint_2(E,gamma_repint,PdivNB,QdivNB,end_i);
    "C3";
    assert(Scheme(gamma_PdivNB) eq E);
    assert(Scheme(gamma_QdivNB) eq E);
    "C4";
    assert(Order(gamma_PdivNB) eq N_A);
    assert(Order(gamma_QdivNB) eq N_A);
    //"gamma(P/N_B)",gamma_PdivNB;
    "C5";
    //construct basis of ker(dual_delta).------
    S_1,S_2:=ell_to_torsion_basis_2(E,b*N_B); 
    assert(Order(S_1) eq b*N_B);
    assert(Order(S_2) eq b*N_B);
    //basis of ker(dual delta).
    bkdd_1,bkdd_2:=image_by_repint_2(E,gamma_repint,S_1,S_2,end_i);
    if Order(bkdd_1) eq b*N_B then
      bkdd:=bkdd_1;
      break count;
    elif Order(bkdd_2) eq b*N_B then
      bkdd:=bkdd_2;
      break count;
    end if;
    if count eq 30 then
      assert(false);
    end if;
  end for;
  assert(Order(bkdd) eq b*N_B);
  "C10";
  
  Ecd,alpha_P,alpha_Q:=elliptic_isogeny_1ptker(E,bkdd,gamma_PdivNB,gamma_QdivNB);
  "C11";
  assert(Order(P) eq Order(alpha_P));
  assert(Order(Q) eq Order(alpha_Q));
  "C12";
  return Ecd,alpha_P,alpha_Q;
end function;


//---------------------------
//main functions.


//calucalte images of isogeny whose kernel are e1,e2.
function component_of_composition(
  l,r,Mat_F,index_t,index_j,
  lv4tnp_dm,lv4tc_e1,lv4tc_e2,lv4tc_e12,
  trp_lv4tc_f1,trp_lv4tc_f2,trp_lv4tc_f12,data_lv4tc)

  time_md:=Time();
  lv4tc_e1,lv4tc_e2,lv4tc_e12:=modify_basis(lv4tnp_dm,l,lv4tc_e1,lv4tc_e2,lv4tc_e12);
  //"modify_basis",Time(time_md);

  time_lincom:=Time();
  lincom_e1e2:=linear_combination(lv4tnp_dm,l,lv4tc_e1,lv4tc_e2,lv4tc_e12); 
  "lin_com for all pts",Time(time_lincom);

  //image of 0.
  time_img:=Time();
  lv4tnp_cd:=lv4tnp_of_codomain(l,r,index_t,index_j,lv4tnp_dm,lv4tc_e1,lv4tc_e2,lv4tc_e12);
  assert(Is_lv4tnp(lv4tnp_cd));
  "img_null_pt_time",Time(time_img);
  
  //image of f1.
  time_img:=Time();
  lv4tc_img_f1:=image_of_point(lincom_e1e2,l,Mat_F,index_t,index_j,lv4tnp_dm,lv4tc_e1,lv4tc_e2,lv4tc_e12,
  trp_lv4tc_f1["f"],trp_lv4tc_f1["f+e1"],trp_lv4tc_f1["f+e2"]);

  "img_non-null_pt_time",Time(time_img);
  //"img_f1_time",Time(time_img);

  //image of f2.
  time_img:=Time();
  lv4tc_img_f2:=image_of_point(lincom_e1e2,l,Mat_F,index_t,index_j,lv4tnp_dm,lv4tc_e1,lv4tc_e2,lv4tc_e12,
  trp_lv4tc_f2["f"],trp_lv4tc_f2["f+e1"],trp_lv4tc_f2["f+e2"]);
  //"img_f2_time",Time(time_img);

  //image of f1+f2(=:f12)
  time_img:=Time();
  lv4tc_img_f12:=image_of_point(lincom_e1e2,l,Mat_F,index_t,index_j,lv4tnp_dm,lv4tc_e1,lv4tc_e2,lv4tc_e12,
  trp_lv4tc_f12["f"],trp_lv4tc_f12["f+e1"],trp_lv4tc_f12["f+e2"]);
  //"img_f12_time",Time(time_img);


  data_img_lv4tc:=[];
  for i in {1..(#data_lv4tc)} do
    data_lv4tc_x:=data_lv4tc[i];
    trp_lv4tc_x   :=data_lv4tc_x["x"];
    trp_lv4tc_xpf1:=data_lv4tc_x["x+f1"];
    trp_lv4tc_xpf2:=data_lv4tc_x["x+f2"];
    data_lv4tc_img_x:=AssociativeArray(); 

    //image of x.
    time_img:=Time();
    data_lv4tc_img_x["x"]:=image_of_point(lincom_e1e2,l,Mat_F,index_t,index_j,lv4tnp_dm,lv4tc_e1,lv4tc_e2,lv4tc_e12,
    trp_lv4tc_x["X"],trp_lv4tc_x["X+e1"],trp_lv4tc_x["X+e2"]);
    //"img_x_time",Time(time_img);

    //image of x+f1.
    time_img:=Time();
    data_lv4tc_img_x["x+f1"]:=image_of_point(lincom_e1e2,l,Mat_F,index_t,index_j,lv4tnp_dm,lv4tc_e1,lv4tc_e2,lv4tc_e12,
    trp_lv4tc_xpf1["X"],trp_lv4tc_xpf1["X+e1"],trp_lv4tc_xpf1["X+e2"]);
    //"img_x+f1_time",Time(time_img);

    //image of x+f2.
    time_img:=Time();
    data_lv4tc_img_x["x+f2"]:=image_of_point(lincom_e1e2,l,Mat_F,index_t,index_j,lv4tnp_dm,lv4tc_e1,lv4tc_e2,lv4tc_e12,
    trp_lv4tc_xpf2["X"],trp_lv4tc_xpf2["X+e1"],trp_lv4tc_xpf2["X+e2"]);
    //"img_x+f2_time",Time(time_img);

    data_img_lv4tc[i]:=data_lv4tc_img_x;
  end for;

  return lv4tnp_cd,lv4tc_img_f1,lv4tc_img_f2,lv4tc_img_f12,data_img_lv4tc;
end function;





//last step version.
function component_of_composition_last(
  l,r,Mat_F,index_t,index_j,
  lv4tnp_dm,lv4tc_e1,lv4tc_e2,lv4tc_e12,
  trp_lv4tc_f1,trp_lv4tc_f2,trp_lv4tc_f12,data_lv4tc)

  time_md:=Time();
  lv4tc_e1,lv4tc_e2,lv4tc_e12:=modify_basis(lv4tnp_dm,l,lv4tc_e1,lv4tc_e2,lv4tc_e12);
  //"modify_basis",Time(time_md);

  time_lincom:=Time();
  lincom_e1e2:=linear_combination(lv4tnp_dm,l,lv4tc_e1,lv4tc_e2,lv4tc_e12); 
  "lin_com for all pts",Time(time_lincom);

  //image of 0.
  time_img:=Time();
  lv4tnp_cd:=lv4tnp_of_codomain(l,r,index_t,index_j,lv4tnp_dm,lv4tc_e1,lv4tc_e2,lv4tc_e12);
  assert(Is_lv4tnp(lv4tnp_cd));
  "img_null_pt_time",Time(time_img);
  
 
  data_img_lv4tc:=[];
  for i in {1..(#data_lv4tc)} do
    data_lv4tc_x:=data_lv4tc[i];
    trp_lv4tc_x   :=data_lv4tc_x["x"];
    data_lv4tc_img_x:=AssociativeArray(); 

    //image of x.
    time_img:=Time();
    data_lv4tc_img_x["x"]:=image_of_point(lincom_e1e2,l,Mat_F,index_t,index_j,lv4tnp_dm,lv4tc_e1,lv4tc_e2,lv4tc_e12,
    trp_lv4tc_x["X"],trp_lv4tc_x["X+e1"],trp_lv4tc_x["X+e2"]);

    "img_non-null_pt_time",Time(time_img);
    //"img_x_time",Time(time_img);

    data_lv4tc_img_x["x+f1"]:=0;
    data_lv4tc_img_x["x+f2"]:=0;
    data_img_lv4tc[i]:=data_lv4tc_img_x;
  end for;

  return lv4tnp_cd,0,0,0,data_img_lv4tc;
end function;





//split to product of ellitpic curve E'*E and represent given points as points on E.
function ell_spliting_2(lv4tnp,lv4tc_1,lv4tc_2,E,zeta_8)
  lv22tnp:=lv4tc_to_lv22tc(lv4tnp);
  assert(lv22tnp[[1,1,1,1]]eq 0);
  lv22tc_1:=lv4tc_to_lv22tc(lv4tc_1);
  lv22tc_2:=lv4tc_to_lv22tc(lv4tc_2);

  E1_lv22tnp:=AssociativeArray();
  E1_lv22tc_1:=AssociativeArray();
  E1_lv22tc_2:=AssociativeArray();

  E2_lv22tnp:=AssociativeArray();
  E2_lv22tc_1:=AssociativeArray();
  E2_lv22tc_2:=AssociativeArray();

  for a,b in {0,1} do
    E1_lv22tnp[[a,b]]:=lv22tnp[[a,0,b,0]];
    E1_lv22tc_1[[a,b]]:=lv22tc_1[[a,0,b,0]];
    E1_lv22tc_2[[a,b]]:=lv22tc_2[[a,0,b,0]];
  end for;
  
  for a,b in {0,1} do
    E2_lv22tnp[[a,b]]:=lv22tnp[[0,a,0,b]];
    E2_lv22tc_1[[a,b]]:=lv22tc_1[[0,a,0,b]];
    E2_lv22tc_2[[a,b]]:=lv22tc_2[[0,a,0,b]];
  end for;

  _,_,_,E1,_,_:=lv22tnp_to_lmd(E1_lv22tnp);
  _,_,_,E2,_,_:=lv22tnp_to_lmd(E2_lv22tnp);

  E_lv22tnp:=AssociativeArray();
  if IsIsomorphic(E,E1) then
    E_lv22tnp:=E1_lv22tnp;
    E_lv22tc_1:=E1_lv22tc_1;
    E_lv22tc_2:=E1_lv22tc_2;
  elif IsIsomorphic(E,E2) then
    E_lv22tnp:=E2_lv22tnp;
    E_lv22tc_1:=E2_lv22tc_1;
    E_lv22tc_2:=E2_lv22tc_2;
  else
    assert(false);
  end if;

  lmd,lv22tnp_lmd,_,E_lmd,j,isss:=lv22tnp_to_lmd(E_lv22tnp);
 
  //theta transformation of "E -> E_lmd".
  M:=theta_trans_same4pow_precomp(E_lv22tnp,lv22tnp_lmd,zeta_8);

  lv22tc_1_lmd:=theta_transform_dim1(E_lv22tc_1,M,zeta_8);
  lv22tc_2_lmd:=theta_transform_dim1(E_lv22tc_2,M,zeta_8);
  assert(Is_on_theta(lv22tnp_lmd,lv22tc_1_lmd));
  assert(Is_on_theta(lv22tnp_lmd,lv22tc_2_lmd));

  u_1,v_1,w_1:=lv22tc_to_uv(lmd,lv22tnp_lmd,lv22tc_1_lmd);
  u_2,v_2,w_2:=lv22tc_to_uv(lmd,lv22tnp_lmd,lv22tc_2_lmd);

  P1:=E_lmd![u_1,v_1,w_1];
  P2:=E_lmd![u_2,v_2,w_2];
  
  _,iso_lmd_0:=IsIsomorphic(E_lmd,E);
  E_P1:=iso_lmd_0(P1);
  E_P2:=iso_lmd_0(P2);

  return E_P1,E_P2;
end function;




//this function is used the last part. 
function correct_aut_2(E_dm,E_cd,N,P_0,Q_0,P_cd,Q_cd,fst_ker1,fst_ker2,scd_ker1,scd_ker2)
  p:=Characteristic(BaseField(E_dm));
  _<t>:=PolynomialRing(GF(p^4));
  cand_ker:=[];
  cand_ker[1]:=fst_ker1;
  cand_ker[2]:=fst_ker2;
  cand_ker[3]:=scd_ker1;
  cand_ker[4]:=scd_ker2;
  for i in {1..4} do
    if cand_ker[i] ne E_dm!0 then
      cand_Ker:=SubgroupScheme(E_dm,&*{(t-(k*cand_ker[i])[1]):k in {1..(N-1)}});
      assert(#cand_Ker eq N);
      cand_E_cd,Edm_to_candEcd:=IsogenyFromKernel(cand_Ker);
      _,candEcd_to_Ecd:=IsIsomorphic(cand_E_cd,E_cd);
      if (candEcd_to_Ecd(Edm_to_candEcd(P_0)) in {P_cd,-P_cd}) and 
         (candEcd_to_Ecd(Edm_to_candEcd(Q_0)) in {Q_cd,-Q_cd}) then
        return cand_ker[i];
      end if;
    end if;
  end for;
  return false;
end function;




//this function is used the last part. 
function Is_correct_cyclic_isogeny(E_dm,E_cd,N,P_0,Q_0,P_cd,Q_cd,ker_1,ker_2)
  p:=Characteristic(BaseField(E_dm));
  _<t>:=PolynomialRing(GF(p^4));
  //saerch generator of cyclic kernel.
  if Order(ker_1) eq N then
    ker:=ker_1;
  elif Order(ker_2) eq N then
    ker:=ker_2;
  else 
    for coff in {1..N-1} do
      if Order(ker_1+coff*ker_2) eq N then
        ker:=ker_1+coff*ker_2;
        break coff;
      end if;
    end for;
  end if;
  E_cd_1,img_P_0,img_Q_0:=elliptic_isogeny_1ptker(E_dm,ker,P_0,Q_0);
  _,iso_cd:=IsIsomorphic(E_cd_1,E_cd);
  if (iso_cd(img_P_0) eq P_cd) and (iso_cd(img_Q_0) eq Q_cd) then
    return true,ker;
  elif (iso_cd(img_P_0) eq -P_cd) and (iso_cd(img_Q_0) eq -Q_cd) then
    return true,ker;
  else
    return false;
  end if;
end function;




//construct x,x+f_1,x+f_2.
function const_trp_x(lmd_0,E_0,lmd_B,E_B,lv4tnp_0,lv22tnp_B,lv4tnp_0B,f1_E0,f1_EB,f2_E0,f2_EB,lv4tc_f1_E0,lv4tc_f2_E0,lv4tc_f1,lv4tc_f2,lv4tc_f12,S)
  //(0,S) in E_0*E_B.--------------
  lv4tc_S:=uvw_to_lv4tc(lmd_B,lv22tnp_B,S[1],S[2],S[3]); 
  assert(Is_on_theta(lv22tnp_B,lv4tc_S));
  lv4tc_0S:=ell_prod_lv4tc(lv4tnp_0,lv4tc_S);

  //theta of S+f_1[2] in E_B.
  lv4tc_Spf1B:=uvw_to_lv4tc(lmd_B,lv22tnp_B,(f1_EB+S)[1],(f1_EB+S)[2],(f1_EB+S)[3]);
  //theta of (0,S)+f_1 in E_0*E_B.
  lv4tc_0Spf1:=ell_prod_lv4tc(lv4tc_f1_E0,lv4tc_Spf1B);
  //assert(get_order(lv4tnp_0B,lv4tc_0S1pe1,170)eq N_A*N_B);

  //theta of S1+f_2[2] in E_B.
  lv4tc_Spf2B:=uvw_to_lv4tc(lmd_B,lv22tnp_B,(f2_EB+S)[1],(f2_EB+S)[2],(f2_EB+S)[3]);
  //theta of (0,S1)+f_2 in E_0*E_B.
  lv4tc_0Spf2:=ell_prod_lv4tc(lv4tc_f2_E0,lv4tc_Spf2B);
  //assert(get_order(lv4tnp_0B,lv4tc_0S1pe2,170)eq N_A*N_B);

  //theta of (0,S1)+s_1*f_1+s_2*f_2 in E_0*E_B.
  tc_0S_lincomf1f2:=x_plus_lincom(lv4tnp_0B,4,lv4tc_f1,lv4tc_f2,lv4tc_f12,lv4tc_0S,lv4tc_0Spf1,lv4tc_0Spf2);

  return lv4tc_0S,lv4tc_0Spf1,lv4tc_0Spf2,tc_0S_lincomf1f2;
end function;






//aux alpha:E_0_4->E_pr.
function main_torsion_attack_3(E_0_4,E_B,E_pr,N_A,N_B,P_A,Q_A,PA_EB,QA_EB,alpha_P_A,alpha_Q_A,precomp_for_N_A,zeta_8)
  time_total:=Time();
  time_prepare:=Time();
  assert(N_A gt N_B);
  assert(P_A in E_0_4);
  assert(Q_A in E_0_4);
  assert(PA_EB in E_B);
  assert(QA_EB in E_B);
  assert(alpha_P_A in E_pr);
  assert(alpha_Q_A in E_pr);
  lmd_0,lv22tnp_0,lv4tnp_0,E_0_4,j_0,isss_0:=E_to_lmd(E_0_4);
  "wait for chaing elliptic curve to another isomorphic one.";
  lmd_B,lv22tnp_B,lv4tnp_B,E_B2,j_B,isss_B,iso_E_B_2:=E_to_lmd(E_B);
  lmd_pr,lv22tnp_pr,lv4tnp_pr,E_pr,j_pr,isss_pr,iso_E_pr:=E_to_lmd(E_pr);
  "fin.";
  assert(isss_0);
  assert(isss_B);
  assert(isss_pr);

  //(N_A,N_A)-isogeny F:E_cd*E_B->E_0*E'_B.
  //basis_KerF:={[alpha(P_A),PA_EB],[alpha(Q_A),QA_EB]}; //in E_cd*E_B.
  //we will call e_1=[alpha(P_A),PA_EB], e_2=[alpha(Q_A),QA_EB].
  //Next we want to calculate  F(0,PA_EB)=(S_1,*), F(0,QA_EB)=(S_2,*), because Ker(phi_B)=<S_1,S_2>.

  //"wait for taking basis of E_B_2[N_B].";
  S1,S2:=ell_to_torsion_basis_2(E_B2,N_B); //attacker will use.
  //"fin.";
  //theta null pt of E_0*E_B.----------------
  lv4tnp_0B:=ell_prod_lv4tc(lv4tnp_pr,lv4tnp_B); 
  assert(Is_lv4tnp(lv4tnp_0B));
  lv22tnp_0B:=lv4tc_to_lv22tc(lv4tnp_0B);
  assert(Is_prod_ell(lv22tnp_0B));
  //basis of Ker(F) is f_1,f_2 in E_0*E_B.
  //f_1 in E_0*E_B.
  f1_E0:=iso_E_pr(alpha_P_A);     //in E_0.
  f1_EB:=iso_E_B_2(PA_EB);    //in E_B2.
  lv4tc_f1_E0:=uvw_to_lv4tc(lmd_pr,lv22tnp_pr,f1_E0[1],f1_E0[2],f1_E0[3]);
  lv4tc_f1_EB:=uvw_to_lv4tc(lmd_B,lv22tnp_B,f1_EB[1],f1_EB[2],f1_EB[3]);
  lv4tc_f1:=ell_prod_lv4tc(lv4tc_f1_E0,lv4tc_f1_EB);
  //assert(IsOrder(lv4tnp_0B,lv4tc_f1,N_A));

  //f_2 in E_0*E_B.
  f2_E0:=iso_E_pr(alpha_Q_A);     //in E_0.
  f2_EB:=iso_E_B_2(QA_EB);    //in E_B2.
  lv4tc_f2_E0:=uvw_to_lv4tc(lmd_pr,lv22tnp_pr,f2_E0[1],f2_E0[2],f2_E0[3]);
  lv4tc_f2_EB:=uvw_to_lv4tc(lmd_B,lv22tnp_B,f2_EB[1],f2_EB[2],f2_EB[3]);
  lv4tc_f2:=ell_prod_lv4tc(lv4tc_f2_E0,lv4tc_f2_EB);
  //assert(IsOrder(lv4tnp_0B,lv4tc_f2,N_A));

  //f_1+f_2 in E_0*E_B.
  f12_E0:=f1_E0+f2_E0;
  f12_EB:=f1_EB+f2_EB;
  lv4tc_f12_E0:=uvw_to_lv4tc(lmd_pr,lv22tnp_pr,f12_E0[1],f12_E0[2],f12_E0[3]);
  lv4tc_f12_EB:=uvw_to_lv4tc(lmd_B,lv22tnp_B,f12_EB[1],f12_EB[2],f12_EB[3]);
  lv4tc_f12:=ell_prod_lv4tc(lv4tc_f12_E0,lv4tc_f12_EB);
  //assert(IsOrder(lv4tnp_0B,lv4tc_f12,N_A));
  //linear combinataion of f_1,f_2.

  //----------------------------------------------
  //S1,S2 is a basis of E_B[N_B].   
  //consider (0,S1),(0,S2) in E_0*E_B.
  //we need these images.
  //construct (0,S_1), (0,S_1)+f_1, (0,S_1)+f_2.
  //"MT9";
  lv4tc_0S1,lv4tc_0S1pf1,lv4tc_0S1pf2,tc_0S1_lincomf1f2:=
  const_trp_x(lmd_pr,E_pr,lmd_B,E_B,lv4tnp_pr,lv22tnp_B,lv4tnp_0B,f1_E0,f1_EB,f2_E0,f2_EB,lv4tc_f1_E0,lv4tc_f2_E0,lv4tc_f1,lv4tc_f2,lv4tc_f12,S1);
  //assert(IsOrder(lv4tnp_0B,lv4tc_0S1,N_B));

  //construct (0,S_2), (0,S_2)+f_1, (0,S_2)+f_2.
  lv4tc_0S2,lv4tc_0S2pf1,lv4tc_0S2pf2,tc_0S2_lincomf1f2:=
  const_trp_x(lmd_pr,E_pr,lmd_B,E_B,lv4tnp_pr,lv22tnp_B,lv4tnp_0B,f1_E0,f1_EB,f2_E0,f2_EB,lv4tc_f1_E0,lv4tc_f2_E0,lv4tc_f1,lv4tc_f2,lv4tc_f12,S2);
  //assert(IsOrder(lv4tnp_0B,lv4tc_0S2,N_B));
  //"MT10";
  //------------------
  lv4tnp_cd:=lv4tnp_0B;

  lv4tc_f1_cd:=lv4tc_f1;
  lv4tc_f2_cd:=lv4tc_f2;
  lv4tc_f12_cd:=lv4tc_f12;

  lv4tc_0S1_cd:=lv4tc_0S1;
  lv4tc_0S1pf1_cd:=lv4tc_0S1pf1;
  lv4tc_0S1pf2_cd:=lv4tc_0S1pf2;

  lv4tc_0S2_cd:=lv4tc_0S2;
  lv4tc_0S2pf1_cd:=lv4tc_0S2pf1;
  lv4tc_0S2pf2_cd:=lv4tc_0S2pf2;

  "prepare time",Time(time_prepare);
  //=========================================

  fac:=fatoriztion_seq(N_A);
  "start isogeny";
  s:=1;
  fac;
  "";

  for i in {1..#fac} do
    time_domain:=Time();

    l:=fac[i];
    kk:=IntegerRing()!(N_A/(s*l));

    //fatoriztion_seq(s),",l=",l,",",fatoriztion_seq(kk);

    //s,",l=",l,",",kk;
    "calculated degree.", fatoriztion_seq(s);
    "calculating degree. l=",l;
    "remaining degree.", fatoriztion_seq(kk);


    assert(s*l*kk eq N_A);
    "l(mod 4)=",(l mod 4);

    Mat_F:=precomp_for_N_A[l]["Mat_F"];
    r:=precomp_for_N_A[l]["r"];
    index_t:=precomp_for_N_A[l]["index_t"];
    index_j:=precomp_for_N_A[l]["index_j"];

    lv4tnp_dm:=lv4tnp_cd;
    lv4tc_f1_dm:=lv4tc_f1_cd;
    lv4tc_f2_dm:=lv4tc_f2_cd;
    lv4tc_f12_dm:=lv4tc_f12_cd;

    //"wait for calculate on the domain.";
    //"MT15";
    lincom_f1f2_dm:=AssociativeArray();
    lincom_f1f2_dm[[1,1]]:=lv4tc_f12_dm;
    //"MT15.1";
    lincom_f1f2_dm[[kk,0]]:=mult2(lv4tnp_dm,kk,lv4tc_f1_dm);
    ///"MT15.2";
    lincom_f1f2_dm[[(kk+1),0]]:=mult2(lv4tnp_dm,kk+1,lv4tc_f1_dm);
    lincom_f1f2_dm[[0,kk]]:=mult2(lv4tnp_dm,kk,lv4tc_f2_dm);
    lincom_f1f2_dm[[0,(kk+1)]]:=mult2(lv4tnp_dm,kk+1,lv4tc_f2_dm);
    //"MT15.3";
    lincom_f1f2_dm[[kk,kk]]:=mult2(lv4tnp_dm,kk,lv4tc_f12_dm);
    //"MT15.4";
    lincom_f1f2_dm[[1,kk]]:=ThreePtLadder_plus(lv4tnp_dm,kk,lv4tc_f2_dm,lv4tc_f1_dm,lv4tc_f12_dm);
    //"MT15.5";
    lincom_f1f2_dm[[1,kk+1]]:=ThreePtLadder_plus(lv4tnp_dm,kk+1,lv4tc_f2_dm,lv4tc_f1_dm,lv4tc_f12_dm);
    lincom_f1f2_dm[[kk,1]]:=ThreePtLadder_plus(lv4tnp_dm,kk,lv4tc_f1_dm,lv4tc_f2_dm,lv4tc_f12_dm);
    lincom_f1f2_dm[[kk+1,1]]:=ThreePtLadder_plus(lv4tnp_dm,kk+1,lv4tc_f1_dm,lv4tc_f2_dm,lv4tc_f12_dm);
    //"MT15.6";
    //"fin.";
   
    //"MT16";

    //assert(IsOrder(lv4tnp_dm,lv4tc_f1_dm,l*kk));
    //assert(IsOrder(lv4tnp_dm,lv4tc_f2_dm,l*kk));
    //assert(IsOrder(lv4tnp_dm,lv4tc_f12_dm,l*kk));

    lv4tc_e1 :=lincom_f1f2_dm[[kk,0]];
    lv4tc_e2 :=lincom_f1f2_dm[[0,kk]];
    lv4tc_e12:=lincom_f1f2_dm[[kk,kk]];

    //"MT16.1";

    //assert(IsOrder(lv4tnp_dm,lv4tc_e1,l));
    //assert(IsOrder(lv4tnp_dm,lv4tc_e2,l));
    //assert(IsOrder(lv4tnp_dm,lv4tc_e12,l));

    lv4tc_0S1_dm   :=lv4tc_0S1_cd;
    lv4tc_0S1pf1_dm:=lv4tc_0S1pf1_cd;
    lv4tc_0S1pf2_dm:=lv4tc_0S1pf2_cd;
    lv4tc_0S2_dm   :=lv4tc_0S2_cd;
    lv4tc_0S2pf1_dm:=lv4tc_0S2pf1_cd;
    lv4tc_0S2pf2_dm:=lv4tc_0S2pf2_cd;

    //assert(IsOrder(lv4tnp_dm,lv4tc_0S1_dm,N_B));
    //assert(IsOrder(lv4tnp_dm,lv4tc_0S2_dm,N_B));

    //S1----------------------------------
    //"MT17";
    tc_0S1_lincomf1f2_dm:=AssociativeArray();
    tc_0S1_lincomf1f2_dm[[0,0]]:=lv4tc_0S1_dm;
    tc_0S1_lincomf1f2_dm[[1,0]]:=lv4tc_0S1pf1_dm;
    tc_0S1_lincomf1f2_dm[[kk,0]]:=ThreePtLadder_plus(lv4tnp_dm,kk,lv4tc_f1_dm,lv4tc_0S1_dm,lv4tc_0S1pf1_dm);
    tc_0S1_lincomf1f2_dm[[kk+1,0]]:=ThreePtLadder_plus(lv4tnp_dm,kk+1,lv4tc_f1_dm,lv4tc_0S1_dm,lv4tc_0S1pf1_dm);
    tc_0S1_lincomf1f2_dm[[0,1]]:=lv4tc_0S1pf2_dm;
    tc_0S1_lincomf1f2_dm[[0,kk]]:=ThreePtLadder_plus(lv4tnp_dm,kk,lv4tc_f2_dm,lv4tc_0S1_dm,lv4tc_0S1pf2_dm);
    tc_0S1_lincomf1f2_dm[[0,kk+1]]:=ThreePtLadder_plus(lv4tnp_dm,kk+1,lv4tc_f2_dm,lv4tc_0S1_dm,lv4tc_0S1pf2_dm);
    //"MT17.1";

    lv4tc_0S1pf1pf2_dm:=calc_xpypz(lv4tnp_dm,
    lv4tc_0S1_dm,lv4tc_f1_dm,lv4tc_f2_dm,
    lv4tc_0S1pf1_dm,lv4tc_0S1pf2_dm,lv4tc_f12_dm);
    //"MT17.2";
    tc_0S1_lincomf1f2_dm[[kk,1]]:=ThreePtLadder_plus(lv4tnp_dm,kk,lv4tc_f1_dm,lv4tc_0S1pf2_dm,lv4tc_0S1pf1pf2_dm);
    tc_0S1_lincomf1f2_dm[[1,kk]]:=ThreePtLadder_plus(lv4tnp_dm,kk,lv4tc_f2_dm,lv4tc_0S1pf1_dm,lv4tc_0S1pf1pf2_dm);
    //"MT18";

    //----------------------------------

    //S2----------------------------------

    tc_0S2_lincomf1f2_dm:=AssociativeArray();
    tc_0S2_lincomf1f2_dm[[0,0]]:=lv4tc_0S2_dm;
    tc_0S2_lincomf1f2_dm[[1,0]]:=lv4tc_0S2pf1_dm;
    tc_0S2_lincomf1f2_dm[[kk,0]]:=ThreePtLadder_plus(lv4tnp_dm,kk,lv4tc_f1_dm,lv4tc_0S2_dm,lv4tc_0S2pf1_dm);
    tc_0S2_lincomf1f2_dm[[kk+1,0]]:=ThreePtLadder_plus(lv4tnp_dm,kk+1,lv4tc_f1_dm,lv4tc_0S2_dm,lv4tc_0S2pf1_dm);
    tc_0S2_lincomf1f2_dm[[0,1]]:=lv4tc_0S2pf2_dm;
    tc_0S2_lincomf1f2_dm[[0,kk]]:=ThreePtLadder_plus(lv4tnp_dm,kk,lv4tc_f2_dm,lv4tc_0S2_dm,lv4tc_0S2pf2_dm);
    tc_0S2_lincomf1f2_dm[[0,kk+1]]:=ThreePtLadder_plus(lv4tnp_dm,kk+1,lv4tc_f2_dm,lv4tc_0S2_dm,lv4tc_0S2pf2_dm);
    //"MT19";

    lv4tc_0S2pf1pf2_dm:=calc_xpypz(lv4tnp_dm,
    lv4tc_0S2_dm,lv4tc_f1_dm,lv4tc_f2_dm,
    lv4tc_0S2pf1_dm,lv4tc_0S2pf2_dm,lv4tc_f12_dm);
    tc_0S2_lincomf1f2_dm[[kk,1]]:=ThreePtLadder_plus(lv4tnp_dm,kk,lv4tc_f1_dm,lv4tc_0S2pf2_dm,lv4tc_0S2pf1pf2_dm);
    tc_0S2_lincomf1f2_dm[[1,kk]]:=ThreePtLadder_plus(lv4tnp_dm,kk,lv4tc_f2_dm,lv4tc_0S2pf1_dm,lv4tc_0S2pf1pf2_dm);
    //"MT20";
    //----------------------------------

 
    //tc_0S1_lincomf1f2_dm:=x_plus_lincom(lv4tnp_dm,(kk+1),lv4tc_f1_dm,lv4tc_f2_dm,lv4tc_f12_dm,lv4tc_0S1_dm,lv4tc_0S1pf1_dm,lv4tc_0S1pf2_dm);

    //tc_0S2_lincomf1f2_dm:=x_plus_lincom(lv4tnp_dm,(kk+1),lv4tc_f1_dm,lv4tc_f2_dm,lv4tc_f12_dm,lv4tc_0S2_dm,lv4tc_0S2pf1_dm,lv4tc_0S2pf2_dm);

    //--------------------------
    trp_lv4tc_f1_dm:=AssociativeArray();
    trp_lv4tc_f1_dm["f"]   :=lv4tc_f1_dm;
    trp_lv4tc_f1_dm["f+e1"]:=lincom_f1f2_dm[[(kk+1),0]];
    trp_lv4tc_f1_dm["f+e2"]:=lincom_f1f2_dm[[1,kk]];
    trp_lv4tc_f2_dm        :=AssociativeArray();
    trp_lv4tc_f2_dm["f"]   :=lv4tc_f2_dm;
    trp_lv4tc_f2_dm["f+e1"]:=lincom_f1f2_dm[[kk,1]];
    trp_lv4tc_f2_dm["f+e2"]:=lincom_f1f2_dm[[0,(kk+1)]];
    trp_lv4tc_f12_dm        :=AssociativeArray();
    trp_lv4tc_f12_dm["f"]   :=lincom_f1f2_dm[[1,1]];
    trp_lv4tc_f12_dm["f+e1"]:=lincom_f1f2_dm[[(kk+1),1]];
    trp_lv4tc_f12_dm["f+e2"]:=lincom_f1f2_dm[[1,(kk+1)]];
    //---------------------------
    data_lv4tc_0S1:=AssociativeArray();
    data_lv4tc_0S1["x"]:=AssociativeArray();
    data_lv4tc_0S1["x"]["X"]   :=tc_0S1_lincomf1f2_dm[[0,0]];
    data_lv4tc_0S1["x"]["X+e1"]:=tc_0S1_lincomf1f2_dm[[kk,0]];
    data_lv4tc_0S1["x"]["X+e2"]:=tc_0S1_lincomf1f2_dm[[0,kk]];
    data_lv4tc_0S1["x+f1"]        :=AssociativeArray();
    data_lv4tc_0S1["x+f1"]["X"]   :=tc_0S1_lincomf1f2_dm[[1,0]];
    data_lv4tc_0S1["x+f1"]["X+e1"]:=tc_0S1_lincomf1f2_dm[[(kk+1),0]];
    data_lv4tc_0S1["x+f1"]["X+e2"]:=tc_0S1_lincomf1f2_dm[[1,kk]];
    data_lv4tc_0S1["x+f2"]        :=AssociativeArray();
    data_lv4tc_0S1["x+f2"]["X"]   :=tc_0S1_lincomf1f2_dm[[0,1]];
    data_lv4tc_0S1["x+f2"]["X+e1"]:=tc_0S1_lincomf1f2_dm[[kk,1]];
    data_lv4tc_0S1["x+f2"]["X+e2"]:=tc_0S1_lincomf1f2_dm[[0,(kk+1)]];

    data_lv4tc_0S2:=AssociativeArray();
    data_lv4tc_0S2["x"]           :=AssociativeArray();
    data_lv4tc_0S2["x"]   ["X"]   :=lv4tc_0S2_cd;
    data_lv4tc_0S2["x"]   ["X+e1"]:=tc_0S2_lincomf1f2_dm[[kk,0]];
    data_lv4tc_0S2["x"]   ["X+e2"]:=tc_0S2_lincomf1f2_dm[[0,kk]];
    data_lv4tc_0S2["x+f1"]        :=AssociativeArray();
    data_lv4tc_0S2["x+f1"]["X"]   :=tc_0S2_lincomf1f2_dm[[1,0]];
    data_lv4tc_0S2["x+f1"]["X+e1"]:=tc_0S2_lincomf1f2_dm[[(kk+1),0]];
    data_lv4tc_0S2["x+f1"]["X+e2"]:=tc_0S2_lincomf1f2_dm[[1,kk]];
    data_lv4tc_0S2["x+f2"]        :=AssociativeArray();
    data_lv4tc_0S2["x+f2"]["X"]   :=tc_0S2_lincomf1f2_dm[[0,1]];
    data_lv4tc_0S2["x+f2"]["X+e1"]:=tc_0S2_lincomf1f2_dm[[kk,1]];
    data_lv4tc_0S2["x+f2"]["X+e2"]:=tc_0S2_lincomf1f2_dm[[0,(kk+1)]];

    data_lv4tc_dm:=[];
    data_lv4tc_dm[1]:=data_lv4tc_0S1;
    data_lv4tc_dm[2]:=data_lv4tc_0S2;
    //-----------------------
    "MT21";

    "calculate time in the domain.", Time(time_domain);

    time_isogeny:=Time();

    if i ne #fac then
      lv4tnp_cd,lv4tc_f1_cd,lv4tc_f2_cd,lv4tc_f12_cd,data_lv4tc_cd:=component_of_composition(l,r,Mat_F,index_t,index_j,lv4tnp_dm,lv4tc_e1,lv4tc_e2,lv4tc_e12,trp_lv4tc_f1_dm,trp_lv4tc_f2_dm,trp_lv4tc_f12_dm,data_lv4tc_dm);
    else
      lv4tnp_cd,lv4tc_f1_cd,lv4tc_f2_cd,lv4tc_f12_cd,data_lv4tc_cd:=component_of_composition_last(l,r,Mat_F,index_t,index_j,lv4tnp_dm,lv4tc_e1,lv4tc_e2,lv4tc_e12,trp_lv4tc_f1_dm,trp_lv4tc_f2_dm,trp_lv4tc_f12_dm,data_lv4tc_dm);
    end if;

    "MT22";
      
    "isogeny time.", Time(time_isogeny);

    assert(Is_lv4tnp(lv4tnp_cd));

    //for next step.
    lv4tc_0S1_cd   :=data_lv4tc_cd[1]["x"];
    lv4tc_0S1pf1_cd:=data_lv4tc_cd[1]["x+f1"];
    lv4tc_0S1pf2_cd:=data_lv4tc_cd[1]["x+f2"];
    lv4tc_0S2_cd   :=data_lv4tc_cd[2]["x"];
    lv4tc_0S2pf1_cd:=data_lv4tc_cd[2]["x+f1"];
    lv4tc_0S2pf2_cd:=data_lv4tc_cd[2]["x+f2"];

    /*
    if (not Is_prod_ell(lv4tnp_cd)) then
      "Jacobian of a curve which has Rosenhein form",
      lv22tnp_to_Ros(to_lv22(lv4tnp_cd));
    end if;
    */

    s:=s*l;
    "";
    "";
  end for;

  "get codomain.";

  time_after:=Time();

  lv4tnp_Y:=lv4tnp_cd;
  //"the number of zero theta",#{key:key in lv22keys|to_lv22(lv4tnp_Y)[key] eq 0};
  assert(Is_prod_ell(lv4tnp_Y));
  lv4tc_0S1_Y:=lv4tc_0S1_cd;
  lv4tc_0S2_Y:=lv4tc_0S2_cd;

  //use theta transformation to split theta structure.
  lv4tnp_Y,lv4tc_0S1_Y,lv4tc_0S2_Y:=to_splitting_theta(lv4tnp_Y,lv4tc_0S1_Y,lv4tc_0S2_Y,zeta_8);

  //-----------------------------

  E_0_img_S1,E_0_img_S2:=ell_spliting_2(lv4tnp_Y,lv4tc_0S1_Y,lv4tc_0S2_Y,E_0_4,zeta_8);

  for iso_E_0_4 in Automorphisms(E_0_4) do
    ker_1:=iso_E_0_4(E_0_img_S1);
    ker_2:=iso_E_0_4(E_0_img_S2);
    assert(ker_1 in E_0_4);
    assert(ker_2 in E_0_4);
    if Is_correct_cyclic_isogeny(E_0_4,E_B,N_B,P_A,Q_A,PA_EB,QA_EB,ker_1,ker_2) then
      _,attacker_kernel:=Is_correct_cyclic_isogeny(E_0_4,E_B,N_B,P_A,Q_A,PA_EB,QA_EB,ker_1,ker_2);
    end if;
  end for;

  assert(attacker_kernel in E_0_4);

  "Calculate time after isogeny", Time(time_after);

  "Total time.",Time(time_total);

  return attacker_kernel;
end function;






//end of torsion_attak6.m
//==============================================







