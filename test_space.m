//for test  setting.

//==================================
//define theta structure of domain.

Ros:=[0,1,3,15,20];  //recommend taking s.t.Ros[1]=0,Ros[2]=1.

Kx<x>:=PolynomialRing(GF(p));
f:=&*[(x-Ros[index]):index in {1..5}];
C:=HyperellipticCurve(f); 
J:=Jacobian(C); 
roots:=RootsInSplittingField(x^2-(Ros[2]-Ros[1]));
R:=roots[1][1];  //R=sqtr(a_2-a_1).Now R=1.
lv22tnp:=Ros_to_lv22tnp(Ros);
lv4tnp:=dbllv22tc_to_lv4tc(lv22tnp);
//==================================



//=====================
//precomputation for l.
l:=5;
Mat_F:=const_Mat_F(l);
//takes a lot time if (l=3 mod4) and l>=7.
r,index_t,index_j:=const_index_t_j(l,Mat_F); 
//====================


//===================
//take kernel and construct level 4 theta null point of codomain.

istr_K:=take_isotropic(J,l); //take one of isotropic subgroup.
assert (Category(istr_K) eq Assoc);
//if you get this assertion error, the base field of J[l] is too big.
kernel_basis:=istr_K["seq_basis"];  
basis1p2:=kernel_basis[1]+kernel_basis[2];

lv4tc1:=Div_to_lv4tc(lv22tnp,kernel_basis[1]); //theta(e_1)
lv4tc2:=Div_to_lv4tc(lv22tnp,kernel_basis[2]); //theta(e_2) 
lv4tc1p2:=Div_to_lv4tc(lv22tnp,basis1p2);      //theta(e_1+e_2)

lv4tnp_B:=lv4tnp_of_codomain(l,r,index_t,index_j,lv4tnp,lv4tc1,lv4tc2,lv4tc1p2);  //theta(0_B)
lv22tnp_B:=lv4tnp_to_lv22tnp(lv4tnp_B);
Ros_B:=lv22tnp_to_Ros(lv22tnp_B);
//=====================

