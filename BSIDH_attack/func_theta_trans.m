//======================================
//theta transformation of dim2.



function mat_to_set(Mat)
  SM1:=Matrix(IntegerRing(),2,2,[Mat[1,1],Mat[1,2], Mat[2,1],Mat[2,2]]);
  SM2:=Matrix(IntegerRing(),2,2,[Mat[1,3],Mat[1,4], Mat[2,3],Mat[2,4]]);
  SM3:=Matrix(IntegerRing(),2,2,[Mat[3,1],Mat[3,2], Mat[4,1],Mat[4,2]]);
  SM4:=Matrix(IntegerRing(),2,2,[Mat[3,3],Mat[3,4], Mat[4,3],Mat[4,4]]);
  M:=[SM1,SM2,SM3,SM4];
  return M;
end function;


function Is_symplectic_g2(M)
  A:=M[1];
  B:=M[2];
  C:=M[3];
  D:=M[4];
  if IsSymmetric(Transpose(A)*C) then
    if IsSymmetric(Transpose(B)*D) then
      if IsOne(Transpose(A)*D-Transpose(C)*B) then
        return true;
      end if;
    end if;
  end if;
  return false;
end function;



function Mab_dim2(M,ab)
  assert(Is_symplectic_g2(M));
  a:=[ab[1],ab[2]];
  b:=[ab[3],ab[4]];
  A:=M[1];
  B:=M[2];
  C:=M[3];
  D:=M[4];
  Mab1_1:=(D[1][1]*a[1]+D[1][2]*a[2])-(C[1][1]*b[1]+C[1][2]*b[2])+(C*Transpose(D))[1][1];
  Mab1_2:=(D[2][1]*a[1]+D[2][2]*a[2])-(C[2][1]*b[1]+C[2][2]*b[2])+(C*Transpose(D))[2][2];
  Mab2_1:=-(B[1][1]*a[1]+B[1][2]*a[2])+(A[1][1]*b[1]+A[1][2]*b[2])+(A*Transpose(B))[1][1];
  Mab2_2:=-(B[2][1]*a[1]+B[2][2]*a[2])+(A[2][1]*b[1]+A[2][2]*b[2])+(A*Transpose(B))[2][2];
  Mab:=[Mab1_1,Mab1_2,Mab2_1,Mab2_2];

  first_vec:=[(D[1][1]*a[1]+D[1][2]*a[2]-C[1][1]*b[1]-C[1][2]*b[2]),(D[2][1]*a[1]+D[2][2]*a[2]-C[2][1]*b[1]-C[2][2]*b[2])];
  second_vec:=[(-B[1][1]*a[1]-B[1][2]*a[2]+A[1][1]*b[1]+A[1][2]*b[2]+2*(C*Transpose(D))[1][1]),(-B[2][1]*a[1]-B[2][2]*a[2]+A[2][1]*b[1]+A[2][2]*b[2]+2*(C*Transpose(D))[2][2])];
  kMab_4mult:=first_vec[1]*second_vec[1]+first_vec[2]*second_vec[2]-(a[1]*b[1]+a[2]*b[2]);
  return Mab,kMab_4mult;
end function;


function red_lv22tc_dim2(ext_ab)
  ab:=[ext_ab[1]mod 2,ext_ab[2]mod 2,ext_ab[3]mod 2,ext_ab[4]mod 2];
  beta:=[IntegerRing()!((ext_ab[3]-ab[3])/2),IntegerRing()!((ext_ab[4]-ab[4])/2)];
  return ab,(-1)^(ab[1]*beta[1]+ab[2]*beta[2]);
end function;


function theta_trans_dim2(lv22tc,M,zeta_8)
  tr_lv22tc:=AssociativeArray();
  for ab in lv22keys do
    Mab,kMab_4mult:=Mab_dim2(M,ab);
    tr_ab,sign:=red_lv22tc_dim2(Mab);
    tr_lv22tc[tr_ab]:=sign*(zeta_8^kMab_4mult)*lv22tc[ab];
  end for;
  assert(Keys(tr_lv22tc) eq lv22keys);
  return tr_lv22tc;
end function;






function to_splitting_theta(lv4tnp,lv4tc_1,lv4tc_2,zeta_8)
  //construct matrix moving 0-valued pt to [1,1,1,1].
  TP:=AssociativeArray();
  for key in even_lv22keys do
    a1:=key[1];
    a2:=key[2];
    b1:=key[3];
    b2:=key[4];
    if key ne [1,1,1,1] then
      TP[key]:=Matrix(IntegerRing(),4,4,[[1,0,b1,0],
      [0,1,0,b2],[a1,0,1,0],[0,a2,0,1]]);
      assert(Is_symplectic_g2(mat_to_set(TP[key])));
    end if;
  end for;
  TP[[1,1,1,1]]:=Matrix(IntegerRing(),4,4,[0,1,0,1, 1,0,1,0, 1,0,1,1, 0,1,1,1]);
  assert(Is_symplectic_g2(mat_to_set(TP[[1,1,1,1]])));

  lv22tnp:=to_lv22(lv4tnp);
  assert(Is_prod_ell(to_lv4(lv22tnp))); //base PPAV is elliptic product.
  set_zero_even:={key:key in even_lv22keys|lv22tnp[key] eq 0};
  assert(#set_zero_even eq 1);
  zero_even:=Random(set_zero_even);
  assert({zero_even} eq set_zero_even);
  if zero_even eq [1,1,1,1] then
    "already splitting.";
    return lv4tnp,lv4tc_1,lv4tc_2;
  else
    lv22tc_1:=to_lv22(lv4tc_1);
    lv22tc_2:=to_lv22(lv4tc_2);
    //--------------
    Mat1:=TP[zero_even]^(-1);
    M1:=mat_to_set(Mat1);
    assert(Is_symplectic_g2(M1));
    t_lv22tnp:=theta_trans_dim2(lv22tnp,M1,zeta_8);
    assert(Is_tnp(t_lv22tnp));
    assert(t_lv22tnp[[0,0,0,0]] eq 0);
    t_lv22tc_1:=theta_trans_dim2(lv22tc_1,M1,zeta_8);
    t_lv22tc_2:=theta_trans_dim2(lv22tc_2,M1,zeta_8);
    //--------------
    Mat2:=TP[[1,1,1,1]];
    M2:=mat_to_set(Mat2);
    assert(Is_symplectic_g2(M2));
    tt_lv22tnp:=theta_trans_dim2(t_lv22tnp,M2,zeta_8);
    assert(Is_tnp(tt_lv22tnp));
    tt_lv22tc_1:=theta_trans_dim2(t_lv22tc_1,M2,zeta_8);
    tt_lv22tc_2:=theta_trans_dim2(t_lv22tc_2,M2,zeta_8);
    assert(tt_lv22tnp[[1,1,1,1]] eq 0);
    return to_lv4(tt_lv22tnp),to_lv4(tt_lv22tc_1),to_lv4(tt_lv22tc_2);
   end if;
end function;


//End of func_theta_trans.m
//======================================

