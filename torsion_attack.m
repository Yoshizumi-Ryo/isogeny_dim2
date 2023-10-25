//only if "a" is square number.

//WLOG, we assume N_A>N_B.
//Over F_(p^4), we use Alice's model of elliptic curve in P^2.

//we consider theta structure given by Thomae formula for Legendre form y^2=x(x-1)(x-lmd).
//---------------
//public infomation.

//p=419.
K:=GF(p);
_<t>:=PolynomialRing(GF(p^4));

N_A:=15;  // N_A|p+1.
N_B:=11;  // N_B|p-1.


//E_0: y^2=x^3-x=x(x-1)(x+1).
lmd_0:=K!(-1);
_,lv22tnp_0,lv4tnp_0,E_0,j_0,isss_0:=lmd_to_lv22tnp(lmd_0);
assert(isss_0);
E_0_4:=BaseChange(E_0,GF(p^4));


//take one basis of E_0[N_A]=(Z/N_A Z)^2.
P_A,Q_A:=ell_to_torsion_basis(E_0_4,N_A);
//take one basis of E_0[N_B]=(Z/N_B Z)^2.
P_B,Q_B:=ell_to_torsion_basis(E_0_4,N_B);






//-------------
//secret selection.

//Alice calculates secretly.
coff_A:=Random({c:c in {0..(N_A-1)}| GCD(c,N_A) eq 1});
R_A:=P_A+coff_A*Q_A;
assert (Order(R_A) eq N_A);
Ker_A:=SubgroupScheme(E_0_4,&*{(t-(k*R_A)[1]):k in {1..(N_A-1)}});
E_A,phi_A:=IsogenyFromKernel(Ker_A); //phi_A: E_0->E_A.
assert(phi_A(R_A) eq E_A!0);
PB_EA:=phi_A(P_B); //image of P_B wrt E_0->E_A.
QB_EA:=phi_A(Q_B); //image of Q_B wrt E_0->E_A.

//Bob calculates secretly.
coff_B:=Random({c: c in {0..(N_B-1)}| GCD(c,N_B) eq 1});
R_B:=P_B+coff_B*Q_B;
assert (Order(R_B) eq N_B);
Ker_B:=SubgroupScheme(E_0_4,&*{(t-(k*R_B)[1]):k in {1..(N_B-1)}});
E_B,phi_B:=IsogenyFromKernel(Ker_B); //phi_B: E_0->E_B.
assert(phi_B(R_B) eq E_B!0);
PA_EB:=phi_B(P_A); //image of P_A wrt E_0->E_B.
QA_EB:=phi_B(Q_A); //image of Q_A wrt E_0->E_B.


//Note that the following data are public.
//E_A,PB_EA,QB_EA,E_B,PA_EB,QA_EB;
//attacker will know R_B;

//attack=================

a:=N_A-N_B;  //a=4.
b:=IntegerRing()!Sqrt(a);  //b=2.
alpha_0:=MultiplicationByMMap(E_0_4,b);  //2倍算 alpha_0:E_0->E_0.

//(N_A,N_A)-isogeny F:E_0*E_B->E_0*E_B.
basis_KerF:={[alpha_0(P_A),PA_EB],[alpha_0(Q_A),QA_EB]}; //in E_0*E_B.

//Next we want to calculate  F(0,PA_EB)=(S_1,*), F(0,QA_EB)=(S_2,*), because Ker(phi_B)=<S_1,S_2>.


//----------------
//we use theta in g=2, l=3,5.

//prepare for E_B.
lmd_B,lv22tnp_B,lv4tnp_B,E_B2,j_B,isss_B,iso_E_B_2:=E_to_lmd(E_B);
assert(isss_B);
//basis of E_B[N_B].
S1,S2:=ell_to_torsion_basis(E_B2,N_B); //attacker will use.


/*
lv4tc_S1:=uv_to_lv4tc(lmd_B,lv22tnp_B,S1[1],S1[2]);
lv22tc_S1:=dim1_lv4tc_to_lv22tc(lv4tc_S1);
uv_S1:=lv22tc_to_uv(lmd_B,lv22tnp_B,lv22tc_S1);
*/



//theta null pt of E_0*E_B.----------------
lv4tnp_0B:=ell_prod_lv4tc(lv4tnp_0,lv4tnp_B); 
assert(Is_lv4tnp(lv4tnp_0B));
lv22tnp_0B:=lv4tc_to_lv22tc(lv4tnp_0B);
assert(Is_prod_ell(lv22tnp_0B));



//basis of Ker(F) is e_1,e_2 in E_0*E_B.
//e_1 in E_0*E_B.
e1_E0:=alpha_0(P_A);     //in E_0.
e1_EB:=iso_E_B_2(PA_EB);    //in E_B2.
lv4tc_e1_E0:=uv_to_lv4tc(lmd_0,lv22tnp_0,e1_E0[1],e1_E0[2]);
lv4tc_e1_EB:=uv_to_lv4tc(lmd_B,lv22tnp_B,e1_EB[1],e1_EB[2]);
lv4tc_e1:=ell_prod_lv4tc(lv4tc_e1_E0,lv4tc_e1_EB);
assert(get_order(lv4tnp_0B,lv4tc_e1,20) eq N_A);



//e_2 in E_0*E_B.
e2_E0:=alpha_0(Q_A);     //in E_0.
e2_EB:=iso_E_B_2(QA_EB);    //in E_B2.
lv4tc_e2_E0:=uv_to_lv4tc(lmd_0,lv22tnp_0,e2_E0[1],e2_E0[2]);
lv4tc_e2_EB:=uv_to_lv4tc(lmd_B,lv22tnp_B,e2_EB[1],e2_EB[2]);
lv4tc_e2:=ell_prod_lv4tc(lv4tc_e2_E0,lv4tc_e2_EB);
assert(get_order(lv4tnp_0B,lv4tc_e2,20) eq N_A);





//e_1+e_2 in E_0*E_B.
e12_E0:=e1_E0+e2_E0;
e12_EB:=e1_EB+e2_EB;
lv4tc_e12_E0:=uv_to_lv4tc(lmd_0,lv22tnp_0,e12_E0[1],e12_E0[2]);
lv4tc_e12_EB:=uv_to_lv4tc(lmd_B,lv22tnp_B,e12_EB[1],e12_EB[2]);
lv4tc_e12:=ell_prod_lv4tc(lv4tc_e12_E0,lv4tc_e12_EB);
assert(get_order(lv4tnp_0B,lv4tc_e12,20) eq N_A);



//test.-------
lv22tc:=dim1_lv4tc_to_lv22tc(lv4tc_e12_E0);
lv22tc_to_uv(lmd_0,lv22tnp_0,lv22tc);
e12_E0;
//-----------




//----------------------------------------------
//S1,S2 is a basis of E_B[N_B].   
//consider (0,S1),(0,S2) in E_0*E_B.
//we need these images.


//(0,S1) in E_0*E_B.--------------
lv4tc_S1:=uv_to_lv4tc(lmd_B,lv22tnp_B,S1[1],S1[2]);
lv4tc_0S1:=ell_prod_lv4tc(lv4tnp_0,lv4tc_S1);
assert(get_order(lv4tnp_0B,lv4tc_0S1,20)eq N_B);
//theta of S1+e_1[2] in E_B.
lv4tc_S1pe1B:=uv_to_lv4tc(lmd_B,lv22tnp_B,(e1_EB+S1)[1],(e1_EB+S1)[2]);
//theta of (0,S1)+e_1 in E_0*E_B.
lv4tc_0S1pe1:=ell_prod_lv4tc(lv4tc_e1_E0,lv4tc_S1pe1B);
assert(get_order(lv4tnp_0B,lv4tc_0S1pe1,170)eq N_A*N_B);
//theta of S1+e_2[2] in E_B2.
lv4tc_S1pe2B:=uv_to_lv4tc(lmd_B,lv22tnp_B,(e2_EB+S1)[1],(e2_EB+S1)[2]);
//theta of (0,S1)+e_2 in E_0*E_B.
lv4tc_0S1pe2:=ell_prod_lv4tc(lv4tc_e2_E0,lv4tc_S1pe2B);
assert(get_order(lv4tnp_0B,lv4tc_0S1pe2,170)eq N_A*N_B);
//tehta of (0,S1)+s_1*e_1+s_2*e_2 in E_0*E_B.
tc_0S1_lincome1e2:=x_plus_lincom(lv4tnp_0B,4,lv4tc_e1,lv4tc_e2,lv4tc_e12,lv4tc_0S1,lv4tc_0S1pe1,lv4tc_0S1pe2);



//(0,S2) in E_0*E_B.--------------------
lv4tc_S2:=uv_to_lv4tc(lmd_B,lv22tnp_B,S2[1],S2[2]);
//theta of (0,S2).
lv4tc_0S2:=ell_prod_lv4tc(lv4tnp_0,lv4tc_S2);
assert(get_order(lv4tnp_0B,lv4tc_0S2,20)eq N_B);
//theta of S2+e_1[2] in E_B.
lv4tc_S2pe1B:=uv_to_lv4tc(lmd_B,lv22tnp_B,(e1_EB+S2)[1],(e1_EB+S2)[2]);
//theta of (0,S2)+e_1 in E_0*E_B.
lv4tc_0S2pe1:=ell_prod_lv4tc(lv4tc_e1_E0,lv4tc_S2pe1B);
assert(get_order(lv4tnp_0B,lv4tc_0S2pe1,175) eq N_A*N_B);

//theta of S2+e_2[2] in E_B2.
lv4tc_S2pe2B:=uv_to_lv4tc(lmd_B,lv22tnp_B,(e2_EB+S2)[1],(e2_EB+S2)[2]);
//theta of (0,S2)+e_2 in E_0*E_B.
lv4tc_0S2pe2:=ell_prod_lv4tc(lv4tc_e2_E0,lv4tc_S2pe2B);

//tehta of (0,S2)+s_1*e_1+s_2*e_2 in E_0*E_B.
tc_0S2_lincome1e2:=x_plus_lincom(lv4tnp_0B,4,lv4tc_e1,lv4tc_e2,lv4tc_e12,lv4tc_0S2,lv4tc_0S2pe1,lv4tc_0S2pe2);


//-------------


//linear combinataion of e_1,e_2.
lincom_e1e2:=linear_combination(lv4tnp_0B,15,lv4tc_e1,lv4tc_e2,lv4tc_e12); 
assert(eq_tc(lv4tnp_0B,lincom_e1e2[[15,15]]));



//from now, calculate kernel and isogeny F:E_0*E_B->E_0*E_B.--------

lv4tc_tre1:=lincom_e1e2[[3,0]];//3*e_1
lv4tc_tre2:=lincom_e1e2[[0,3]];//3*e_2
lv4tc_tre12:=lincom_e1e2[[3,3]];//3*(e_1+e_2)
assert(eq_tc(mult(lv4tnp_0B,5,lv4tc_tre1),lv4tnp_0B));
assert(eq_tc(mult(lv4tnp_0B,5,lv4tc_tre2),lv4tnp_0B));
assert(eq_tc(mult(lv4tnp_0B,5,lv4tc_tre12),lv4tnp_0B));

//prepare for l_1=5 isogeny E_0*E_B->X.---------------------
l_1:=5;
Mat_F_1:=const_Mat_F(l_1);
r_1,index_t_1,index_j_1:=const_index_t_j(l_1,Mat_F_1); 

lv4tc_tre1,lv4tc_tre2,lv4tc_tre12:=modify_basis(lv4tnp_0B,l_1,lv4tc_tre1,lv4tc_tre2,lv4tc_tre12);
lincom_trie1e2:=linear_combination(lv4tnp_0B,l_1,lv4tc_tre1,lv4tc_tre2,lv4tc_tre12); 


//compute iamge of the following 10 pts for E_0*E_B->X.-------------------

//image of 0.
lv4tnp_X:=lv4tnp_of_codomain(l_1,r_1,index_t_1,index_j_1,lv4tnp_0B,lv4tc_tre1,lv4tc_tre2,lv4tc_tre12);
assert(Is_lv4tnp(lv4tnp_X));
Is_prod_ell(lv4tnp_X); 
//false.i.e.Jacobian.

//---------------------


//image of e_1.
lv4tc_e1_X:=image_of_point(lincom_trie1e2,l_1,Mat_F_1,index_t_1,index_j_1,lv4tnp_0B,lv4tc_tre1,lv4tc_tre2,lv4tc_tre12,lv4tc_e1,lincom_e1e2[[4,0]],lincom_e1e2[[1,3]]);
assert(get_order(lv4tnp_X,lv4tc_e1_X,20)eq 3);


//image of e_2.
lv4tc_e2_X:=image_of_point(lincom_trie1e2,l_1,Mat_F_1,index_t_1,index_j_1,lv4tnp_0B,lv4tc_tre1,lv4tc_tre2,lv4tc_tre12,lv4tc_e2,lincom_e1e2[[3,1]],lincom_e1e2[[0,4]]);
assert(get_order(lv4tnp_X,lv4tc_e2_X,20)eq 3);

//image of e_1+e_2.
lv4tc_e12_X:=image_of_point(lincom_trie1e2,l_1,Mat_F_1,index_t_1,index_j_1,lv4tnp_0B,lv4tc_tre1,lv4tc_tre2,lv4tc_tre12,lv4tc_e12,lincom_e1e2[[4,1]],lincom_e1e2[[1,4]]);
assert(get_order(lv4tnp_X,lv4tc_e12_X,20)eq 3);

//--------------------
//image of (0,S1).
lv4tc_0S1_X:=image_of_point(lincom_trie1e2,l_1,Mat_F_1,index_t_1,index_j_1,lv4tnp_0B,lv4tc_tre1,lv4tc_tre2,lv4tc_tre12,
lv4tc_0S1,tc_0S1_lincome1e2[[3,0]],tc_0S1_lincome1e2[[0,3]]);
assert(get_order(lv4tnp_X,lv4tc_0S1_X,170) eq N_B);

//image of (0,S1)+e_1.
lv4tc_0S1pe1_X:=image_of_point(lincom_trie1e2,l_1,Mat_F_1,index_t_1,index_j_1,lv4tnp_0B,lv4tc_tre1,lv4tc_tre2,lv4tc_tre12,
tc_0S1_lincome1e2[[1,0]],tc_0S1_lincome1e2[[4,0]],tc_0S1_lincome1e2[[1,3]]);
//assert(get_order(img_lv4tnp,img_0S1pe1,170)eq 33);

//image of (0,S1)+e_2.
lv4tc_0S1pe2_X:=image_of_point(lincom_trie1e2,l_1,Mat_F_1,index_t_1,index_j_1,lv4tnp_0B,lv4tc_tre1,lv4tc_tre2,lv4tc_tre12,
tc_0S1_lincome1e2[[0,1]],tc_0S1_lincome1e2[[3,1]],tc_0S1_lincome1e2[[0,4]]);
//assert(get_order(img_lv4tnp,img_0S1pe2,170)eq 33);

//----------------------
//image of (0,S2).
lv4tc_0S2_X:=image_of_point(lincom_trie1e2,l_1,Mat_F_1,index_t_1,index_j_1,lv4tnp_0B,lv4tc_tre1,lv4tc_tre2,lv4tc_tre12,
lv4tc_0S2,tc_0S2_lincome1e2[[3,0]],tc_0S2_lincome1e2[[0,3]]);
assert(get_order(lv4tnp_X,lv4tc_0S2_X,30)eq N_B);

//image of (0,S2)+e_1.
lv4tc_0S2pe1_X:=image_of_point(lincom_trie1e2,l_1,Mat_F_1,index_t_1,index_j_1,lv4tnp_0B,lv4tc_tre1,lv4tc_tre2,lv4tc_tre12,
tc_0S2_lincome1e2[[1,0]],tc_0S2_lincome1e2[[4,0]],tc_0S2_lincome1e2[[1,3]]);
//get_order(img_lv4tnp,img_0S2pe1,170); //33

//image of (0,S2)+e_2.
lv4tc_0S2pe2_X:=image_of_point(lincom_trie1e2,l_1,Mat_F_1,index_t_1,index_j_1,lv4tnp_0B,lv4tc_tre1,lv4tc_tre2,lv4tc_tre12,
tc_0S2_lincome1e2[[0,1]],tc_0S2_lincome1e2[[3,1]],tc_0S2_lincome1e2[[0,4]]);
//get_order(img_lv4tnp,img_0S2pe2,170);//33.




//-----------------------
//prepare the next isogeny of deg=3 X->E_0*E_B.

l_2:=3;
Mat_F_2:=const_Mat_F(l_2);
r_2,index_t_2,index_j_2:=const_index_t_j(l_2,Mat_F_2); 

lv4tc_e1_X,lv4tc_e2_X,lv4tc_e12_X:=modify_basis(lv4tnp_X,l_2,lv4tc_e1_X,lv4tc_e2_X,lv4tc_e12_X);

lincom_e1e2_X:=linear_combination(lv4tnp_X,l_2,lv4tc_e1_X,lv4tc_e2_X,lv4tc_e12_X);



//=================================
//calculate the image of (0,S1),)(0,S2) for X->Y=E_0*E_B.


//image of 0.
lv4tnp_Y:=lv4tnp_of_codomain(l_2,r_2,index_t_2,index_j_2,lv4tnp_X,lv4tc_e1_X,lv4tc_e2_X,lv4tc_e12_X);
assert(Is_lv4tnp(lv4tnp_Y));
Is_prod_ell(lv4tnp_Y); 
//true i.e. elliptic.

//image of image of (0,S1).
lv4tc_0S1_Y:=image_of_point(lincom_e1e2_X,l_2,Mat_F_2,index_t_2,index_j_2,lv4tnp_X,lv4tc_e1_X,lv4tc_e2_X,lv4tc_e12_X,lv4tc_0S1_X,lv4tc_0S1pe1_X,lv4tc_0S1pe2_X);

//image of image of (0,S2).
lv4tc_0S2_Y:=image_of_point(lincom_e1e2_X,l_2,Mat_F_2,index_t_2,index_j_2,lv4tnp_X,lv4tc_e1_X,lv4tc_e2_X,lv4tc_e12_X,lv4tc_0S2_X,lv4tc_0S2pe1_X,lv4tc_0S2pe2_X);



//some check.
assert(N_B mod (get_order(lv4tnp_Y,lv4tc_0S1_Y,30)) eq 0);
assert(N_B mod (get_order(lv4tnp_Y,lv4tc_0S2_Y,30)) eq 0);


//----------------------------
//decompose the codomain to the product of elliptic.

lv22tnp_Y:=lv4tc_to_lv22tc(lv4tnp_Y);
lv22tc_0S1:=lv4tc_to_lv22tc(lv4tc_0S1_Y);
lv22tc_0S2:=lv4tc_to_lv22tc(lv4tc_0S2_Y);

eq_tc(lv22tnp_0B,lv22tnp_Y);  //false.
eq_tc(lv4tnp_0B,lv4tnp_Y);  //false.




lv22tnp_E0_cod:=AssociativeArray();
lv22tc_E0_cod_S1:=AssociativeArray();
lv22tc_E0_cod_S2:=AssociativeArray();

lv22tnp_EB_cod:=AssociativeArray();lv22tc_EB_cod_S1:=AssociativeArray();
lv22tc_EB_cod_S2:=AssociativeArray();

for a,b in {0,1} do
  lv22tnp_E0_cod[[a,b]]:=lv22tnp_Y[[0,a,0,b]];
  lv22tc_E0_cod_S1[[a,b]]:=lv22tc_0S1[[0,a,0,b]];
  lv22tc_E0_cod_S2[[a,b]]:=lv22tc_0S2[[0,a,0,b]];

  lv22tnp_EB_cod[[a,b]]:=lv22tnp_Y[[a,0,b,0]];
  lv22tc_EB_cod_S1[[a,b]]:=lv22tc_0S1[[a,0,b,0]];
  lv22tc_EB_cod_S2[[a,b]]:=lv22tc_0S2[[a,0,b,0]];
end for;



//------------------------------


lmd_cd0,lv22tnp_lmcd0,lv4tnp_lmcd0,E_lmcd0,j_lmcd0,isss_lmcd0
:=lv22tnp_to_lmd(lv22tnp_E0_cod);


lmd_cdB,lv22tnp_lmcdB,lv4tnp_lmcdB,E_lmcdB,j_lmcdB,isss_lmcdB
:=lv22tnp_to_lmd(lv22tnp_EB_cod);



//theta transformation.
//E_0 ----------------------------------------

lmd_cd0,lv22tnp_lmcd0,lv4tnp_lmcd0,E_lmcd0,j_lmcd0,isss_lmcd0
:=lv22tnp_to_lmd(lv22tnp_E0_cod);

assert(j_0 eq j_lmcd0);
assert(same_theta_lmd(lmd_0,lmd_cd0));

assert((lv22tnp_E0_cod[[0,1]]/lv22tnp_E0_cod[[0,0]])^4 eq
(lv22tnp_lmcd0[[0,1]]/lv22tnp_lmcd0[[0,0]])^4);
assert((lv22tnp_E0_cod[[1,0]]/lv22tnp_E0_cod[[0,0]])^4 eq
(lv22tnp_lmcd0[[1,0]]/lv22tnp_lmcd0[[0,0]])^4);

//theta transformation of "E_0_cod -> E_0_lmd_cod".
M:=theta_trans_same4pow(lv22tnp_E0_cod,lv22tnp_lmcd0);

assert(eq_tc_dim1(lv22tnp_lmcd0,theta_transform_dim1(lv22tnp_E0_cod,M)));
lv22tc_lmcd0_S1:=theta_transform_dim1(lv22tc_E0_cod_S1,M);
lv22tc_lmcd0_S2:=theta_transform_dim1(lv22tc_E0_cod_S2,M);
assert(Is_on_theta(lv22tnp_lmcd0,lv22tc_lmcd0_S1));
assert(Is_on_theta(lv22tnp_lmcd0,lv22tc_lmcd0_S2));


//finish theta transformation E_0_cod->E_lmcd0.
//------------------------------------
//Last step. we connect E_lmcd0->E_0.

u_img_S1,v_img_S1:=lv22tc_to_uv(lmd_cd0,lv22tnp_lmcd0,lv22tc_lmcd0_S1);
u_img_S2,v_img_S2:=lv22tc_to_uv(lmd_cd0,lv22tnp_lmcd0,lv22tc_lmcd0_S2);


img_S1:=E_lmcd0![u_img_S1,v_img_S1,1];
img_S2:=E_lmcd0![u_img_S2,v_img_S2,1];


_,iso_cd_to_0:=IsIsomorphic(E_lmcd0,E_0_4);
img_img_S1:=iso_cd_to_0(img_S1);
img_img_S2:=iso_cd_to_0(img_S2);


{k*R_B:k in {0..10}} eq {k_1*img_img_S1+k_2*img_img_S2: k_1,k_2 in {0..10}};
//Attacker got kernel of phi_B !!!!!

