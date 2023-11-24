//==============================================
//start of torsion_attack6.m


//auxi. funcs.



//This is not Cornacchia Alg, but the same result. 
function Cornacchia(M)
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
function FullRepInt(M)
  assert(M gt p);
  assert(p mod 4 eq 3);
  for i in {1..50} do
    md:=Floor(Sqrt(4*M/p));  //m'
    zd:=Random({-md..md});   //z'
    mdd:=Floor(Sqrt((4*M/p)-zd^2)); //m"
    td:=Random({-mdd..mdd});  //t'
    Md:=4*M-p*(zd^2+td^2);  //M'
    if Cornacchia(Md) then
      _,xd,yd:=Cornacchia(Md);
      if ((xd-td) mod 2 eq 0) and ((yd-zd) mod 2 eq 0) then
        x:=IntegerRing()!((xd-td)/2);
        y:=IntegerRing()!((yd-zd)/2);
        z:=zd;
        t:=td;
        deg:=((xd^2+yd^2+p*(zd^2+td^2)) div 4);
        assert(deg eq M);
        return [x,y,z,t]; //x+y*i+z*((i+j)/2)+t*((1+k)/2).
      end if;
    end if;
  end for;
  "we cannot find.";
  return false;
end function;




//return image of d-torsion basis for given rep_normal_basis.
function image_by_repint(E,rep_int,P,Q)
  _<x>:=PolynomialRing(GF(p^4));
  Em_4:=EllipticCurve(x^3-x);
  Ep_4:=EllipticCurve(x^3+x);
  assert(E eq Em_4);
  _,iso_mp:=IsIsomorphic(Em_4,Ep_4);
  iso_pm:=Inverse(iso_mp);
  Pp:=iso_mp(P);
  Qp:=iso_mp(Q);
  end_i:=Automorphisms(Ep_4)[2];
  assert(end_i^2 eq NegationMap(Ep_4));  //-1=i^2.
  end_j:=FrobeniusMap(Ep_4);
  end_k:=end_i*end_j;
  assert(#{end_i(R)+end_j(R):R in Points(TorsionSubgroupScheme(Ep_4,2))} eq 1);
  x:=rep_int[1];
  y:=rep_int[2];
  z:=rep_int[3];
  t:=rep_int[4];
  //x+y*i+z*((i+j)/2)+t*((1+k)/2).
  hPp:=Pp/2;
  hQp:=Qp/2;
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





//P,Q are basis of E[N_A].
function construct_auxiliary_img(E,N_A,N_B,P,Q)
  assert(Order(P)eq N_A);
  assert(Order(Q)eq N_A);
  _<x>:=PolynomialRing(GF(p^4));
  Em_4:=EllipticCurve(x^3-x);
  assert(E eq Em_4);
  assert(Scheme(P) eq Em_4);
  assert(Scheme(Q) eq Em_4);
  assert(N_A gt N_B);
  a:=N_A-N_B;
  gamma_repint:=FullRepInt(a*N_B); 
  PB:=P/N_B;
  QB:=Q/N_B;
  gamma_PB,gamma_QB:=image_by_repint(E,gamma_repint,PB,QB);
  
  //construct ker(dual_delta).=============
  S_1,S_2:=ell_to_torsion_basis_2(E,a*N_B); 
  assert(Order(S_1) eq a*N_B);
  assert(Order(S_2) eq a*N_B);
  T_1,T_2:=image_by_repint(E,gamma_repint,S_1,S_2);
  T_1:=E!T_1;
  T_2:=E!T_2;
  aT1:=a*T_1;
  aT2:=a*T_2;
  assert(IsDivisibleBy(N_B,Order(aT1)));
  assert(IsDivisibleBy(N_B,Order(aT2)));
  pts_ker_dual_delta:={k_1*aT1+k_2*aT2 :k_1,k_2 in {0..N_B}};
  assert(#pts_ker_dual_delta eq N_B);
  sch_ker_dual_delta:=SubgroupScheme(E,&*{(x-pt[1]):pt in (pts_ker_dual_delta diff {E!0})});
  assert(#sch_ker_dual_delta eq N_B);
  Ecd,dual_delta:=IsogenyFromKernel(sch_ker_dual_delta);  
  assert(Degree(dual_delta) eq N_B);
  //==================================
  alpha_P:=(dual_delta(gamma_PB));
  alpha_Q:=(dual_delta(gamma_QB));
  assert(IsDivisibleBy(Order(P),Order(alpha_P)));
  assert(IsDivisibleBy(Order(Q),Order(alpha_Q)));
  return Ecd,alpha_P,alpha_Q;
end function;



//---------------------------
//main functions.


//calucalte images of isogeny whose kernel are e1,e2.
function component_of_composition(
  l,r,Mat_F,index_t,index_j,
  lv4tnp_dm,lv4tc_e1,lv4tc_e2,lv4tc_e12,
  trp_lv4tc_f1,trp_lv4tc_f2,trp_lv4tc_f12,data_lv4tc)

  lv4tc_e1,lv4tc_e2,lv4tc_e12:=modify_basis(lv4tnp_dm,l,lv4tc_e1,lv4tc_e2,lv4tc_e12);
  lincom_e1e2:=linear_combination(lv4tnp_dm,l,lv4tc_e1,lv4tc_e2,lv4tc_e12); 

  //image of 0.
  lv4tnp_cd:=lv4tnp_of_codomain(l,r,index_t,index_j,lv4tnp_dm,lv4tc_e1,lv4tc_e2,lv4tc_e12);
  assert(Is_lv4tnp(lv4tnp_cd));
  //image of f1.
  lv4tc_img_f1:=image_of_point(lincom_e1e2,l,Mat_F,index_t,index_j,lv4tnp_dm,lv4tc_e1,lv4tc_e2,lv4tc_e12,
  trp_lv4tc_f1["f"],trp_lv4tc_f1["f+e1"],trp_lv4tc_f1["f+e2"]);
  //image of f2.
  lv4tc_img_f2:=image_of_point(lincom_e1e2,l,Mat_F,index_t,index_j,lv4tnp_dm,lv4tc_e1,lv4tc_e2,lv4tc_e12,
  trp_lv4tc_f2["f"],trp_lv4tc_f2["f+e1"],trp_lv4tc_f2["f+e2"]);
  //image of f1+f2(=:f12)
  lv4tc_img_f12:=image_of_point(lincom_e1e2,l,Mat_F,index_t,index_j,lv4tnp_dm,lv4tc_e1,lv4tc_e2,lv4tc_e12,
  trp_lv4tc_f12["f"],trp_lv4tc_f12["f+e1"],trp_lv4tc_f12["f+e2"]);

  data_img_lv4tc:=[];
  for i in {1..(#data_lv4tc)} do
    data_lv4tc_x:=data_lv4tc[i];
    trp_lv4tc_x   :=data_lv4tc_x["x"];
    trp_lv4tc_xpf1:=data_lv4tc_x["x+f1"];
    trp_lv4tc_xpf2:=data_lv4tc_x["x+f2"];
    data_lv4tc_img_x:=AssociativeArray(); 
    //image of x.
    data_lv4tc_img_x["x"]:=image_of_point(lincom_e1e2,l,Mat_F,index_t,index_j,lv4tnp_dm,lv4tc_e1,lv4tc_e2,lv4tc_e12,
    trp_lv4tc_x["X"],trp_lv4tc_x["X+e1"],trp_lv4tc_x["X+e2"]);
    //image of x+f1.
    data_lv4tc_img_x["x+f1"]:=image_of_point(lincom_e1e2,l,Mat_F,index_t,index_j,lv4tnp_dm,lv4tc_e1,lv4tc_e2,lv4tc_e12,
    trp_lv4tc_xpf1["X"],trp_lv4tc_xpf1["X+e1"],trp_lv4tc_xpf1["X+e2"]);
    //image of x+f2.
    data_lv4tc_img_x["x+f2"]:=image_of_point(lincom_e1e2,l,Mat_F,index_t,index_j,lv4tnp_dm,lv4tc_e1,lv4tc_e2,lv4tc_e12,
    trp_lv4tc_xpf2["X"],trp_lv4tc_xpf2["X+e1"],trp_lv4tc_xpf2["X+e2"]);
    data_img_lv4tc[i]:=data_lv4tc_img_x;
  end for;
  return lv4tnp_cd,lv4tc_img_f1,lv4tc_img_f2,lv4tc_img_f12,data_img_lv4tc;
end function;







//split to product of ellitpic curve E'*E and represent given points as points on E.
function ell_spliting(lv4tnp,lv4tc_1,lv4tc_2,E)
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

  _<x>:=PolynomialRing(GF(p));
  zeta_8:=RootsInSplittingField(x^8-1)[2][1];
  assert(zeta_8^4 eq -1);
  
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
  fst_E_P1:=iso_lmd_0(P1);
  fst_E_P2:=iso_lmd_0(P2);

  aut_i_E:=Automorphisms(E)[2];
  scd_E_P1:=aut_i_E(fst_E_P1);
  scd_E_P2:=aut_i_E(fst_E_P2);
  return fst_E_P1,fst_E_P2,scd_E_P1,scd_E_P2;
end function;









//this function is used the last part. 
function correct_aut_2(E_dm,E_cd,N,P_0,Q_0,P_cd,Q_cd,fst_ker1,fst_ker2,scd_ker1,scd_ker2)
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









//使わない.
function main_torsion_attack_2(E_0,E_B,N_A,N_B,P_A,Q_A,PA_EB,QA_EB,alpha_P_A,alpha_Q_A,Prime_Fac_N_A)

  E_0_4:=BaseChange(E_0,GF(p^4));
  lmd_0,lv22tnp_0,lv4tnp_0,E_0,j_0,isss_0:=E_to_lmd(E_0);
  assert(isss_0);
  lmd_B,lv22tnp_B,lv4tnp_B,E_B2,j_B,isss_B,iso_E_B_2:=E_to_lmd(E_B);
  assert(isss_B);
  //basis of E_B[N_B].

  //(N_A,N_A)-isogeny F:E_0*E_B->E_0*E_B.
  //basis_KerF:={[alpha_0(P_A),PA_EB],[alpha_0(Q_A),QA_EB]}; //in E_0*E_B.
  //we will call e_1=[alpha_0(P_A),PA_EB], e_2=[alpha_0(Q_A),QA_EB].
  //Next we want to calculate  F(0,PA_EB)=(S_1,*), F(0,QA_EB)=(S_2,*), because Ker(phi_B)=<S_1,S_2>.

  S1,S2:=ell_to_torsion_basis(E_B2,N_B); //attacker will use.

  //theta null pt of E_0*E_B.----------------
  lv4tnp_0B:=ell_prod_lv4tc(lv4tnp_0,lv4tnp_B); 
  assert(Is_lv4tnp(lv4tnp_0B));
  lv22tnp_0B:=lv4tc_to_lv22tc(lv4tnp_0B);
  assert(Is_prod_ell(lv22tnp_0B));

  //basis of Ker(F) is f_1,f_2 in E_0*E_B.
  //f_1 in E_0*E_B.
  f1_E0:=alpha_P_A;     //in E_0.
  f1_EB:=iso_E_B_2(PA_EB);    //in E_B2.
  lv4tc_f1_E0:=uvw_to_lv4tc(lmd_0,lv22tnp_0,f1_E0[1],f1_E0[2],f1_E0[3]);
  lv4tc_f1_EB:=uvw_to_lv4tc(lmd_B,lv22tnp_B,f1_EB[1],f1_EB[2],f1_EB[3]);
  lv4tc_f1:=ell_prod_lv4tc(lv4tc_f1_E0,lv4tc_f1_EB);
  //assert(get_order(lv4tnp_0B,lv4tc_f1,20) eq N_A);

  //f_2 in E_0*E_B.
  f2_E0:=alpha_Q_A;     //in E_0.
  f2_EB:=iso_E_B_2(QA_EB);    //in E_B2.
  lv4tc_f2_E0:=uvw_to_lv4tc(lmd_0,lv22tnp_0,f2_E0[1],f2_E0[2],f2_E0[3]);
  lv4tc_f2_EB:=uvw_to_lv4tc(lmd_B,lv22tnp_B,f2_EB[1],f2_EB[2],f2_EB[3]);
  lv4tc_f2:=ell_prod_lv4tc(lv4tc_f2_E0,lv4tc_f2_EB);
  //assert(get_order(lv4tnp_0B,lv4tc_f2,20) eq N_A);

  //f_1+f_2 in E_0*E_B.
  f12_E0:=f1_E0+f2_E0;
  f12_EB:=f1_EB+f2_EB;
  lv4tc_f12_E0:=uvw_to_lv4tc(lmd_0,lv22tnp_0,f12_E0[1],f12_E0[2],f12_E0[3]);
  lv4tc_f12_EB:=uvw_to_lv4tc(lmd_B,lv22tnp_B,f12_EB[1],f12_EB[2],f12_EB[3]);
  lv4tc_f12:=ell_prod_lv4tc(lv4tc_f12_E0,lv4tc_f12_EB);
  //assert(get_order(lv4tnp_0B,lv4tc_f12,20) eq N_A);

  //linear combinataion of f_1,f_2.
  lincom_f1f2:=linear_combination(lv4tnp_0B,4,lv4tc_f1,lv4tc_f2,lv4tc_f12); 

  //----------------------------------------------
  //S1,S2 is a basis of E_B[N_B].   
  //consider (0,S1),(0,S2) in E_0*E_B.
  //we need these images.

  lv4tc_0S1,lv4tc_0S1pf1,lv4tc_0S1pf2,tc_0S1_lincomf1f2:=
  const_trp_x(lmd_0,E_0,lmd_B,E_B,lv4tnp_0,lv22tnp_B,lv4tnp_0B,f1_E0,f1_EB,f2_E0,f2_EB,lv4tc_f1_E0,lv4tc_f2_E0,lv4tc_f1,lv4tc_f2,lv4tc_f12,S1);

  lv4tc_0S2,lv4tc_0S2pf1,lv4tc_0S2pf2,tc_0S2_lincomf1f2:=
  const_trp_x(lmd_0,E_0,lmd_B,E_B,lv4tnp_0,lv22tnp_B,lv4tnp_0B,f1_E0,f1_EB,f2_E0,f2_EB,lv4tc_f1_E0,lv4tc_f2_E0,lv4tc_f1,lv4tc_f2,lv4tc_f12,S2);

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

  //------------------------
  s:=1;
  while s lt N_A do
    l:=Max({l:l in Prime_Fac_N_A|((IntegerRing()!(N_A/s)) mod l eq 0)});
    Mat_F:=const_Mat_F(l);
    r,index_t,index_j:=const_index_t_j(l,Mat_F); 
    kk:=IntegerRing()!(N_A/(s*l));

    s,l,kk;

    assert(s*l*kk eq N_A);

    lv4tnp_dm:=lv4tnp_cd;
    lv4tc_f1_dm:=lv4tc_f1_cd;
    lv4tc_f2_dm:=lv4tc_f2_cd;
    lv4tc_f12_dm:=lv4tc_f12_cd;
    lincom_f1f2_dm:=linear_combination(lv4tnp_dm,(kk+1),lv4tc_f1_dm,lv4tc_f2_dm,lv4tc_f12_dm); 

    assert(get_order(lv4tnp_dm,lv4tc_f1_dm,200) eq l*kk);
    assert(get_order(lv4tnp_dm,lv4tc_f2_dm,200) eq l*kk);
    assert(get_order(lv4tnp_dm,lv4tc_f12_dm,200) eq l*kk);
    assert(eq_Assoc(lincom_f1f2_dm[[1,1]],lv4tc_f12_dm));

    lv4tc_e1 :=lincom_f1f2_dm[[kk,0]];
    lv4tc_e2 :=lincom_f1f2_dm[[0,kk]];
    lv4tc_e12:=lincom_f1f2_dm[[kk,kk]];

    assert(get_order(lv4tnp_dm,lv4tc_e1,200) eq l);
    assert(get_order(lv4tnp_dm,lv4tc_e2,200) eq l);
    assert(get_order(lv4tnp_dm,lv4tc_e12,200) eq l);

    lv4tc_0S1_dm   :=lv4tc_0S1_cd;
    lv4tc_0S1pf1_dm:=lv4tc_0S1pf1_cd;
    lv4tc_0S1pf2_dm:=lv4tc_0S1pf2_cd;
    lv4tc_0S2_dm   :=lv4tc_0S2_cd;
    lv4tc_0S2pf1_dm:=lv4tc_0S2pf1_cd;
    lv4tc_0S2pf2_dm:=lv4tc_0S2pf2_cd;

    assert(get_order(lv4tnp_dm,lv4tc_0S1_dm,200) eq N_B);
    assert(get_order(lv4tnp_dm,lv4tc_0S2_dm,200) eq N_B);
 
    tc_0S1_lincomf1f2_dm:=x_plus_lincom(lv4tnp_dm,(kk+1),lv4tc_f1_dm,lv4tc_f2_dm,lv4tc_f12_dm,lv4tc_0S1_dm,lv4tc_0S1pf1_dm,lv4tc_0S1pf2_dm);
    tc_0S2_lincomf1f2_dm:=x_plus_lincom(lv4tnp_dm,(kk+1),lv4tc_f1_dm,lv4tc_f2_dm,lv4tc_f12_dm,lv4tc_0S2_dm,lv4tc_0S2pf1_dm,lv4tc_0S2pf2_dm);

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

    lv4tnp_cd,lv4tc_f1_cd,lv4tc_f2_cd,lv4tc_f12_cd,data_lv4tc_cd:=component_of_composition(l,r,Mat_F,index_t,index_j,lv4tnp_dm,lv4tc_e1,lv4tc_e2,lv4tc_e12,
    trp_lv4tc_f1_dm,trp_lv4tc_f2_dm,trp_lv4tc_f12_dm,
    data_lv4tc_dm);

    assert(Is_lv4tnp(lv4tnp_cd));
    assert(get_order(lv4tnp_cd,lv4tc_f1_cd,200) eq kk);

    //for next step.
    lv4tc_0S1_cd   :=data_lv4tc_cd[1]["x"];
    lv4tc_0S1pf1_cd:=data_lv4tc_cd[1]["x+f1"];
    lv4tc_0S1pf2_cd:=data_lv4tc_cd[1]["x+f2"];
    lv4tc_0S2_cd   :=data_lv4tc_cd[2]["x"];
    lv4tc_0S2pf1_cd:=data_lv4tc_cd[2]["x+f1"];
    lv4tc_0S2pf2_cd:=data_lv4tc_cd[2]["x+f2"];
    s:=s*l;
    
    assert(get_order(lv4tnp_cd,lv4tc_0S1_cd,200) eq N_B);
    assert(get_order(lv4tnp_cd,lv4tc_0S2_cd,200) eq N_B);

  end while;

  lv4tnp_Y:=lv4tnp_cd;
  assert(Is_prod_ell(lv4tnp_Y));
  lv22tnp_Y:=lv4tc_to_lv22tc(lv4tnp_Y);
  assert((lv22tnp_Y[[1,1,1,1]]) eq 0);
  lv4tc_0S1_Y:=lv4tc_0S1_cd;
  lv4tc_0S2_Y:=lv4tc_0S2_cd;

  //=================================

  fst_E_0_img_S1,fst_E_0_img_S2,scd_E_0_img_S1,scd_E_0_img_S2:=ell_spliting(lv4tnp_Y,lv4tc_0S1_Y,lv4tc_0S2_Y,E_0_4);

  attacker_kernel:=correct_aut_2(E_0_4,E_B,N_B,P_A,Q_A,PA_EB,QA_EB,fst_E_0_img_S1,fst_E_0_img_S2,scd_E_0_img_S1,scd_E_0_img_S2);

  return attacker_kernel;
end function;



//aux alpha:E_0_4->E_pr.
function main_torsion_attack_3(E_0_4,E_B,E_pr,N_A,N_B,P_A,Q_A,PA_EB,QA_EB,alpha_P_A,alpha_Q_A,Prime_Fac_N_A)
  assert(N_A gt N_B);
  assert(P_A in E_0_4);
  assert(Q_A in E_0_4);
  assert(PA_EB in E_B);
  assert(QA_EB in E_B);
  assert(alpha_P_A in E_pr);
  assert(alpha_Q_A in E_pr);

  lmd_0,lv22tnp_0,lv4tnp_0,E_0_4,j_0,isss_0:=E_to_lmd(E_0_4);
  lmd_B,lv22tnp_B,lv4tnp_B,E_B2,j_B,isss_B,iso_E_B_2:=E_to_lmd(E_B);
  lmd_pr,lv22tnp_pr,lv4tnp_pr,E_pr,j_pr,isss_pr,iso_E_pr:=E_to_lmd(E_pr);
  assert(isss_0);
  assert(isss_B);
  assert(isss_pr);

  //(N_A,N_A)-isogeny F:E_cd*E_B->E_0*E'_B.
  //basis_KerF:={[alpha(P_A),PA_EB],[alpha(Q_A),QA_EB]}; //in E_cd*E_B.
  //we will call e_1=[alpha(P_A),PA_EB], e_2=[alpha(Q_A),QA_EB].
  //Next we want to calculate  F(0,PA_EB)=(S_1,*), F(0,QA_EB)=(S_2,*), because Ker(phi_B)=<S_1,S_2>.

  S1,S2:=ell_to_torsion_basis(E_B2,N_B); //attacker will use.

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
  //assert(get_order(lv4tnp_0B,lv4tc_f1,20) eq N_A);

  //f_2 in E_0*E_B.
  f2_E0:=iso_E_pr(alpha_Q_A);     //in E_0.
  f2_EB:=iso_E_B_2(QA_EB);    //in E_B2.
  lv4tc_f2_E0:=uvw_to_lv4tc(lmd_pr,lv22tnp_pr,f2_E0[1],f2_E0[2],f2_E0[3]);
  lv4tc_f2_EB:=uvw_to_lv4tc(lmd_B,lv22tnp_B,f2_EB[1],f2_EB[2],f2_EB[3]);
  lv4tc_f2:=ell_prod_lv4tc(lv4tc_f2_E0,lv4tc_f2_EB);
  //assert(get_order(lv4tnp_0B,lv4tc_f2,20) eq N_A);

  //f_1+f_2 in E_0*E_B.
  f12_E0:=f1_E0+f2_E0;
  f12_EB:=f1_EB+f2_EB;
  lv4tc_f12_E0:=uvw_to_lv4tc(lmd_pr,lv22tnp_pr,f12_E0[1],f12_E0[2],f12_E0[3]);
  lv4tc_f12_EB:=uvw_to_lv4tc(lmd_B,lv22tnp_B,f12_EB[1],f12_EB[2],f12_EB[3]);
  lv4tc_f12:=ell_prod_lv4tc(lv4tc_f12_E0,lv4tc_f12_EB);
  //assert(get_order(lv4tnp_0B,lv4tc_f12,20) eq N_A);

  //linear combinataion of f_1,f_2.
  lincom_f1f2:=linear_combination(lv4tnp_0B,4,lv4tc_f1,lv4tc_f2,lv4tc_f12); 

  //----------------------------------------------
  //S1,S2 is a basis of E_B[N_B].   
  //consider (0,S1),(0,S2) in E_0*E_B.
  //we need these images.

  //construct (0,S_1), (0,S_1)+f_1, (0,S_1)+f_2.
  lv4tc_0S1,lv4tc_0S1pf1,lv4tc_0S1pf2,tc_0S1_lincomf1f2:=
  const_trp_x(lmd_pr,E_pr,lmd_B,E_B,lv4tnp_pr,lv22tnp_B,lv4tnp_0B,f1_E0,f1_EB,f2_E0,f2_EB,lv4tc_f1_E0,lv4tc_f2_E0,lv4tc_f1,lv4tc_f2,lv4tc_f12,S1);

  //construct (0,S_2), (0,S_2)+f_1, (0,S_2)+f_2.
  lv4tc_0S2,lv4tc_0S2pf1,lv4tc_0S2pf2,tc_0S2_lincomf1f2:=
  const_trp_x(lmd_pr,E_pr,lmd_B,E_B,lv4tnp_pr,lv22tnp_B,lv4tnp_0B,f1_E0,f1_EB,f2_E0,f2_EB,lv4tc_f1_E0,lv4tc_f2_E0,lv4tc_f1,lv4tc_f2,lv4tc_f12,S2);

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

  //------------------------
  "start";
  s:=1;
  while s lt N_A do
    l:=Max({l:l in Prime_Fac_N_A|((IntegerRing()!(N_A/s)) mod l eq 0)});
    Mat_F:=const_Mat_F(l);
    r,index_t,index_j:=const_index_t_j(l,Mat_F); 
    kk:=IntegerRing()!(N_A/(s*l));

    s,l,kk;

    assert(s*l*kk eq N_A);

    lv4tnp_dm:=lv4tnp_cd;
    lv4tc_f1_dm:=lv4tc_f1_cd;
    lv4tc_f2_dm:=lv4tc_f2_cd;
    lv4tc_f12_dm:=lv4tc_f12_cd;
    lincom_f1f2_dm:=linear_combination(lv4tnp_dm,(kk+1),lv4tc_f1_dm,lv4tc_f2_dm,lv4tc_f12_dm); 

    assert(get_order(lv4tnp_dm,lv4tc_f1_dm,200) eq l*kk);
    assert(get_order(lv4tnp_dm,lv4tc_f2_dm,200) eq l*kk);
    assert(get_order(lv4tnp_dm,lv4tc_f12_dm,200) eq l*kk);
    assert(eq_Assoc(lincom_f1f2_dm[[1,1]],lv4tc_f12_dm));

    lv4tc_e1 :=lincom_f1f2_dm[[kk,0]];
    lv4tc_e2 :=lincom_f1f2_dm[[0,kk]];
    lv4tc_e12:=lincom_f1f2_dm[[kk,kk]];

    assert(get_order(lv4tnp_dm,lv4tc_e1,200) eq l);
    assert(get_order(lv4tnp_dm,lv4tc_e2,200) eq l);
    assert(get_order(lv4tnp_dm,lv4tc_e12,200) eq l);

    lv4tc_0S1_dm   :=lv4tc_0S1_cd;
    lv4tc_0S1pf1_dm:=lv4tc_0S1pf1_cd;
    lv4tc_0S1pf2_dm:=lv4tc_0S1pf2_cd;
    lv4tc_0S2_dm   :=lv4tc_0S2_cd;
    lv4tc_0S2pf1_dm:=lv4tc_0S2pf1_cd;
    lv4tc_0S2pf2_dm:=lv4tc_0S2pf2_cd;

    assert(get_order(lv4tnp_dm,lv4tc_0S1_dm,200) eq N_B);
    assert(get_order(lv4tnp_dm,lv4tc_0S2_dm,200) eq N_B);
 
    tc_0S1_lincomf1f2_dm:=x_plus_lincom(lv4tnp_dm,(kk+1),lv4tc_f1_dm,lv4tc_f2_dm,lv4tc_f12_dm,lv4tc_0S1_dm,lv4tc_0S1pf1_dm,lv4tc_0S1pf2_dm);
    tc_0S2_lincomf1f2_dm:=x_plus_lincom(lv4tnp_dm,(kk+1),lv4tc_f1_dm,lv4tc_f2_dm,lv4tc_f12_dm,lv4tc_0S2_dm,lv4tc_0S2pf1_dm,lv4tc_0S2pf2_dm);

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

    lv4tnp_cd,lv4tc_f1_cd,lv4tc_f2_cd,lv4tc_f12_cd,data_lv4tc_cd:=component_of_composition(l,r,Mat_F,index_t,index_j,lv4tnp_dm,lv4tc_e1,lv4tc_e2,lv4tc_e12,
    trp_lv4tc_f1_dm,trp_lv4tc_f2_dm,trp_lv4tc_f12_dm,
    data_lv4tc_dm);

    assert(Is_lv4tnp(lv4tnp_cd));
    assert(get_order(lv4tnp_cd,lv4tc_f1_cd,200) eq kk);

    //for next step.
    lv4tc_0S1_cd   :=data_lv4tc_cd[1]["x"];
    lv4tc_0S1pf1_cd:=data_lv4tc_cd[1]["x+f1"];
    lv4tc_0S1pf2_cd:=data_lv4tc_cd[1]["x+f2"];
    lv4tc_0S2_cd   :=data_lv4tc_cd[2]["x"];
    lv4tc_0S2pf1_cd:=data_lv4tc_cd[2]["x+f1"];
    lv4tc_0S2pf2_cd:=data_lv4tc_cd[2]["x+f2"];
    s:=s*l;
    
    assert(get_order(lv4tnp_cd,lv4tc_0S1_cd,200) eq N_B);
    assert(get_order(lv4tnp_cd,lv4tc_0S2_cd,200) eq N_B);

  end while;

  "get codomain.";

  lv4tnp_Y:=lv4tnp_cd;
  assert(Is_prod_ell(lv4tnp_Y));
  lv4tc_0S1_Y:=lv4tc_0S1_cd;
  lv4tc_0S2_Y:=lv4tc_0S2_cd;

  //use theta transformation to split theta structure.
  lv4tnp_Y,lv4tc_0S1_Y,lv4tc_0S2_Y:=to_splitting_theta(lv4tnp_Y,lv4tc_0S1_Y,lv4tc_0S2_Y);

  //=================================

  fst_E_0_img_S1,fst_E_0_img_S2,scd_E_0_img_S1,scd_E_0_img_S2:=ell_spliting(lv4tnp_Y,lv4tc_0S1_Y,lv4tc_0S2_Y,E_0_4);

  attacker_kernel:=correct_aut_2(E_0_4,E_B,N_B,P_A,Q_A,PA_EB,QA_EB,fst_E_0_img_S1,fst_E_0_img_S2,scd_E_0_img_S1,scd_E_0_img_S2);

  return attacker_kernel;
end function;

//end of torsion_attak6.m
//==============================================







