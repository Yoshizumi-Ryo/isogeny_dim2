//==================================
//define theta structure of domain.

Ros:=[0,1,3,4,5];  //recommend taking s.t.Ros[1]=0,Ros[2]=1.

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

//takes time if l=3 mod4. (not l=3)
r,index_t,index_j:=const_index_t_j(l,Mat_F); 
//====================

//===================
//take kernel and construct lv4tnp of codomain.

istr_K:=take_isotropic(J,l); //take one of isotropic subgroup.
assert (Category(istr_K) eq Assoc);
//if you get this assertion error, the base field of J[l] is too big.
kernel_basis:=istr_K["seq_basis"];
e1:=kernel_basis[1];
e2:=kernel_basis[2];
e1pe2:=e1+e2;

tc_e1:=Div_to_lv4tc(lv22tnp,e1); //theta(e_1)
tc_e2:=Div_to_lv4tc(lv22tnp,e2); //theta(e_2) 
tc_e1pe2:=Div_to_lv4tc(lv22tnp,e1pe2);      //theta(e_1+e_2)

lv4tnp_B:=lv4tnp_of_codomain(l,r,index_t,index_j,lv4tnp,tc_e1,tc_e2,tc_e1pe2);  //theta(0_B)

//--------------------------------------------
//precomputation for compute image of point.

J:=BaseChange(J,BaseField(Parent(kernel_basis[1])));
tc_e1,tc_e2,tc_e1pe2:=modify_basis(lv4tnp,l,tc_e1,tc_e2,tc_e1pe2);
lincom_e1e2:=linear_combination(lv4tnp,l,tc_e1,tc_e2,tc_e1pe2); 
//=====================================
//image of general point.

Dx:=Random(J);
tc_x:=Div_to_lv4tc(lv22tnp,Dx);
tc_xpe1:=Div_to_lv4tc(lv22tnp,Dx+e1);
tc_xpe2:=Div_to_lv4tc(lv22tnp,Dx+e2);

img_x:=image_of_point_new(lincom_e1e2,l,Mat_F,index_t,index_j,lv4tnp,tc_e1,tc_e2,tc_e1pe2,tc_x,tc_xpe1,tc_xpe2);

//---------------------------
