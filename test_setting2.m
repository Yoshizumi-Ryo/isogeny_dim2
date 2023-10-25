//==================================
//define theta structure of domain.

Ros:=[0,1,2,3,4];  //recommend taking s.t.Ros[1]=0,Ros[2]=1.
f:=&*[(x-Ros[index]):index in {1..5}];
C:=HyperellipticCurve(f); 
J:=Jacobian(C); 
roots:=RootsInSplittingField(x^2-(Ros[2]-Ros[1]));
R:=roots[1][1];  //R=sqtr(a_2-a_1).Now R=1.
lv22tnp:=Ros_to_lv22tnp(Ros);
lv4tnp:=lv22tc_to_lv4tc(lv22tnp);
assert(Is_lv4tnp(lv4tnp));
//==================================

Is_prod_ell(lv4tnp); //false.

prob_able(Ros,J,10000);



//=====================
//precomputation for l.
l:=5;
Mat_F:=const_Mat_F(l);

//takes time if l=3 mod4. (not l=3)
r,index_t,index_j:=const_index_t_j(l,Mat_F); 
//====================

L<z>:=GF(p^4);

//===================
//take kernel and construct lv4tnp of codomain.

istr_K:=take_one_isotropic(J,l,12); 
//take one of isotropic subgroup.
assert (Category(istr_K) eq Assoc);
//if you get this assertion error, the base field of J[l] is too big.
kernel_basis:=istr_K["seq_basis"];
e1:=kernel_basis[1];
e2:=kernel_basis[2];
e1pe2:=e1+e2;

tc_e1:=Div_to_lv4tc_2(Ros,lv22tnp,e1); //theta(e_1)
tc_e2:=Div_to_lv4tc_2(Ros,lv22tnp,e2); //theta(e_2) 
tc_e1pe2:=Div_to_lv4tc_2(Ros,lv22tnp,e1pe2);      //theta(e_1+e_2)
lv4tnp_B:=lv4tnp_of_codomain(l,r,index_t,index_j,lv4tnp,tc_e1,tc_e2,tc_e1pe2); 
assert(Is_lv4tnp(lv4tnp_B));
/*
lv22tnp_B:=lv4tc_to_lv22tc(lv4tnp_B);
Ros_B:=lv22tnp_to_Ros(lv22tnp_B);  
Fld_B:=Parent(Ros_B[3]);
PolFld_B<x_B>:=PolynomialRing(Fld_B);
f_B:=&*[(x_B-Ros_B[index]):index in {1..5}];
C_B:=HyperellipticCurve(f_B); 
J_B:=Jacobian(C_B); 
*/
//--------------------------------------------
//precomputation for compute image of point.
J:=BaseChange(J,istr_K["field"]);
tc_e1,tc_e2,tc_e1pe2:=modify_basis(lv4tnp,l,tc_e1,tc_e2,tc_e1pe2);
lincom_e1e2:=linear_combination(lv4tnp,l,tc_e1,tc_e2,tc_e1pe2); 
//=====================================



//===============================
//image of general point.
Dx:=Random(J);
tc_x   :=Div_to_lv4tc_2(Ros,lv22tnp,Dx);
tc_xpe1:=Div_to_lv4tc_2(Ros,lv22tnp,Dx+e1);
tc_xpe2:=Div_to_lv4tc_2(Ros,lv22tnp,Dx+e2);



t0:=Time();
img_x:=image_of_point(lincom_e1e2,l,Mat_F,index_t,index_j,lv4tnp,tc_e1,tc_e2,tc_e1pe2,tc_x,tc_xpe1,tc_xpe2);
Time(t0);
//===============================


//準同型性の確認.
Dx:=Random(J);
tc_x   :=Div_to_lv4tc_2(Ros,lv22tnp,Dx);
tc_xpe1:=Div_to_lv4tc_2(Ros,lv22tnp,Dx+e1);
tc_xpe2:=Div_to_lv4tc_2(Ros,lv22tnp,Dx+e2);
img_x:=image_of_point(lincom_e1e2,l,Mat_F,index_t,index_j,lv4tnp,tc_e1,tc_e2,tc_e1pe2,tc_x,tc_xpe1,tc_xpe2);

Dy:=Random(J);
tc_y   :=Div_to_lv4tc_2(Ros,lv22tnp,Dy);
tc_ype1:=Div_to_lv4tc_2(Ros,lv22tnp,Dy+e1);
tc_ype2:=Div_to_lv4tc_2(Ros,lv22tnp,Dy+e2);
img_y:=image_of_point(lincom_e1e2,l,Mat_F,index_t,index_j,lv4tnp,tc_e1,tc_e2,tc_e1pe2,tc_y,tc_ype1,tc_ype2);

Dxmy:=Dx-Dy;
tc_xmy   :=Div_to_lv4tc_2(Ros,lv22tnp,Dxmy);
tc_xmype1:=Div_to_lv4tc_2(Ros,lv22tnp,Dxmy+e1);
tc_xmype2:=Div_to_lv4tc_2(Ros,lv22tnp,Dxmy+e2);
img_xmy:=image_of_point(lincom_e1e2,l,Mat_F,index_t,index_j,lv4tnp,tc_e1,tc_e2,tc_e1pe2,tc_xmy,tc_xmype1,tc_xmype2);

Dxpy:=Dx+Dy;
tc_xpy   :=Div_to_lv4tc_2(Ros,lv22tnp,Dxpy);
tc_xpype1:=Div_to_lv4tc_2(Ros,lv22tnp,Dxpy+e1);
tc_xpype2:=Div_to_lv4tc_2(Ros,lv22tnp,Dxpy+e2);
img_xpy:=image_of_point(lincom_e1e2,l,Mat_F,index_t,index_j,lv4tnp,tc_e1,tc_e2,tc_e1pe2,tc_xpy,tc_xpype1,tc_xpype2);


img_xpy_2:=add(lv4tnp_B,img_x,img_y,img_xmy);
eq_tc(img_xpy,img_xpy_2);




//========================

function All_Ros(p)
  Ros_set:={};
  for R3 in [2..(p-3)] do
    for R4 in [(R3+1)..(p-2)] do
      for R5 in [(R4+1)..(p-1)] do
        new_Ros:=[0,1,R3,R4,R5];
        Ros_set join:={new_Ros};
      end for;
    end for;
  end for;
  return Ros_set;
end function;





//----------------------------------
Dx:=Random(J);
tc_x:=Div_to_lv4tc_2(Ros,lv22tnp,Dx);
Dy:=Random(J);
tc_y:=Div_to_lv4tc_2(Ros,lv22tnp,Dy);
Dz:=Random(J);
tc_z:=Div_to_lv4tc_2(Ros,lv22tnp,Dz);
Dxy:=Dx+Dy;
tc_xy:=Div_to_lv4tc_2(Ros,lv22tnp,Dxy);
Dxz:=Dx+Dz;
tc_xz:=Div_to_lv4tc_2(Ros,lv22tnp,Dxz);
Dyz:=Dy+Dz;
tc_yz:=Div_to_lv4tc_2(Ros,lv22tnp,Dyz);
Dxyz:=Dx+Dy+Dz;
tc_xyz:=Div_to_lv4tc_2(Ros,lv22tnp,Dxyz);


tc_xyz_2:=calc_xpypz(lv4tnp,tc_x,tc_y,tc_z,tc_xy,tc_xz,tc_yz);

eq_tc(tc_xyz,tc_xyz_2);








