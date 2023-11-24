//これはあまり書き換えるな!!


//only if "a" is square number.

//WLOG, we assume N_A>N_B.
//Over F_(p^4), we use Alice's model of elliptic curve in P^2.

//we consider theta structure given by Thomae formula for Legendre form y^2=x(x-1)(x-lmd).
//---------------
//public infomation.





assert((p mod 4) eq 3);
K:=GF(p);
_<t>:=PolynomialRing(GF(p^4));

N_A:=9;  // N_A|p+1.
N_B:=5;  // N_B|p+1.
Prime_Fac_N_A:={3};  //all prime factors of N_A.


//E_0: y^2=x^3-x=x(x-1)(x+1).
lmd_0:=K!(-1);
_,lv22tnp_0,lv4tnp_0,E_0,j_0,isss_0:=lmd_to_lv22tnp(lmd_0);
assert(isss_0);
E_0_4:=BaseChange(E_0,GF(p^4));



//take one basis of E_0[N_A]=(Z/N_A Z)^2.
P_A,Q_A:=ell_to_torsion_basis(E_0_4,N_A);
//take one basis of E_0[N_B]=(Z/N_B Z)^2.
P_B,Q_B:=ell_to_torsion_basis(E_0_4,N_B);



//===============================
//Bob calculates secretly.
coff_B:=Random({c: c in {0..(N_B-1)}});
R_B:=E_0_4!(P_B+coff_B*Q_B);
assert (Order(R_B) eq N_B);
Ker_B:=SubgroupScheme(E_0_4,&*{(t-(k*R_B)[1]):k in {1..(N_B-1)}});
assert(#Ker_B eq N_B);
E_B,phi_B:=IsogenyFromKernel(Ker_B); //phi_B: E_0->E_B.
assert(phi_B(R_B) eq E_B!0);
PA_EB:=phi_B(P_A); //image of P_A wrt E_0->E_B.
QA_EB:=phi_B(Q_A); //image of Q_A wrt E_0->E_B.


//Note that the following data are public.
//E_A,PB_EA,QB_EA,E_B,PA_EB,QA_EB;



//attack=================
/*
//construct auxiliary image.

a:=N_A-N_B;  //a=16
b:=IntegerRing()!Sqrt(a);  //b=4.
alpha_0:=MultiplicationByMMap(E_0_4,b);  //4倍算 alpha_0:E_0->E_0.
alpha_P_A:=alpha_0(P_A);
alpha_Q_A:=alpha_0(Q_A);

atk_gen:=E_0_4!main_torsion_attack_2(E_0,E_B,N_A,N_B,P_A,Q_A,PA_EB,QA_EB,alpha_P_A,alpha_Q_A,Prime_Fac_N_A);  


Atk_Ker_phB:={k*atk_gen:k in {0..N_B}};  //Attacker.
Bob_Ker_phB:={k*E_0_4!R_B:k in {0..N_B}};      //Bob.

Atk_Ker_phB eq Bob_Ker_phB;
*/
//=======================




E_pr,alpha_P_A,alpha_Q_A:=construct_auxiliary_img(E_0_4,N_A,N_B,P_A,Q_A);



atk_gen:=E_0_4!main_torsion_attack_3(E_0_4,E_B,E_pr,N_A,N_B,P_A,Q_A,PA_EB,QA_EB,alpha_P_A,alpha_Q_A,Prime_Fac_N_A);

Atk_Ker_phB:={k*atk_gen:k in {0..N_B}};  //Attacker.
Bob_Ker_phB:={k*E_0_4!R_B:k in {0..N_B}};      //Bob.

Atk_Ker_phB eq Bob_Ker_phB;




/*
//symp 行列を大量生成

bit_symp44:={};
for cp in CartesianPower({0,1},16) do
  A:=Matrix(2,2,[[cp[1],cp[2]],[cp[3],cp[4]]]);
  B:=Matrix(2,2,[[cp[5],cp[6]],[cp[7],cp[8]]]);
  C:=Matrix(2,2,[[cp[9],cp[10]],[cp[11],cp[12]]]);
  D:=Matrix(2,2,[[cp[13],cp[14]],[cp[15],cp[16]]]);
  M:=[A,B,C,D];
  if Is_symplectic_g2(M) then
    bit_symp44 join:={M};
  end if;
end for;




for key in even_lv22keys do
  a1:=key[1];
  a2:=key[2];
  b1:=key[3];
  b2:=key[4];
  for M in bit_symp44 do
    A:=M[1];
    B:=M[2];
    C:=M[3];
    D:=M[4];
    if 

*/

