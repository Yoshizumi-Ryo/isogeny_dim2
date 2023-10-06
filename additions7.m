
//==============================================
//Start of additions6.m

/*
  Here, it is written about add and mult. for affine lift/ 
  We only think n=4, g=2, so the number of cordinate is n^g=16.
  As usual, the Keys is {[i,j]:i,j in {0..3}}.
  "lx" is affine lift of x, "lxmy" is one of x-y.
  cf.[80]LR12,Alogorithm3.3
*/

/*
  The following function is  to caluculate of u.
  "u" is associative array whose keys are [[0,0],[0,0]],...,[[3,3],[1,1]] of 16*4=64 picies.
*/



 //this function is used in the next function.
 //return sum_{t}(chi(t)*P_{i+t}*Q_{j+t}).
function term(chi,i,j,P,Q) 
  sum:=0;  //wanted.
  for t in set_t do
    sum:=sum+(voc[[chi,t]]*P[ipt[[i,t]]]*Q[ipt[[j,t]]]);
  end for;
  return sum;
end function; 



//we can check if A=[P_1,...,P_8] is Rimeann position.
function Riemann_Relation(A)
  for cr in CartesianProduct(set_chi,sub_RP_i) do
    i2:=[(cr[2][5][1]-cr[2][1][1]) mod 4,(cr[2][5][2]-cr[2][1][2]) mod 4];
    j2:=[(cr[2][5][1]-cr[2][2][1]) mod 4,(cr[2][5][2]-cr[2][2][2]) mod 4];
    k2:=[(cr[2][5][1]-cr[2][3][1]) mod 4,(cr[2][5][2]-cr[2][3][2]) mod 4];
    l2:=[(cr[2][5][1]-cr[2][4][1]) mod 4,(cr[2][5][2]-cr[2][4][2]) mod 4];

    LHS:=term(cr[1],cr[2][1],cr[2][2],A[1],A[2])*term(cr[1],cr[2][3],cr[2][4],A[3],A[4]);

    RHS:=term(cr[1],i2,j2,A[5],A[6])*term(cr[1],k2,l2,A[7],A[8]);

    if LHS ne RHS then 
      return false;      
    end if;
  end for;   
  return true;
end function; 



//this function gives only necessary condition.
//the following function determine if level 4 theta null pt is.
function Is_lv4tnp(lv4tnp)
  for i1 in {0..3} do
    for i2 in {0..3} do
      if lv4tnp[[i1,i2]] ne lv4tnp[[(4-i1) mod 4,(4-i2) mod 4]] then
        return false;
      end if;
    end for;
  end for;

  A:=[lv4tnp,lv4tnp,lv4tnp,lv4tnp,lv4tnp,lv4tnp,lv4tnp,lv4tnp];
  return Riemann_Relation(A);
end function;





//check about [LR12] Theorem 3.2.
function LR12Thm32(alxpy,alxmy,al0,alx,aly) 
  TF:=true;
  for cr in CartesianProduct(set_chi,sub_RP_i) do
    //(i,j,k,l;m) is Riemann position.
    chi:=cr[1];

    i:=cr[2][1];
    j:=cr[2][2];
    k:=cr[2][3];
    l:=cr[2][4];
    m:=cr[2][5];
    i_d:=[(m[1]-i[1])mod 4,(m[2]-i[2])mod 4];  //i'
    j_d:=[(m[1]-j[1])mod 4,(m[2]-j[2])mod 4];  //j'
    k_d:=[(m[1]-k[1])mod 4,(m[2]-k[2])mod 4];  //k'
    l_d:=[(m[1]-l[1])mod 4,(m[2]-l[2])mod 4];  //l'
    m_i_d:=[(-i_d[1])mod 4,(-i_d[2]) mod 4]; //-i'

    LHS:=term(chi,i,j,alxpy,alxmy)*term(chi,k,l,al0,al0);
    RHS:=term(chi,m_i_d,j_d,aly,aly)*term(chi,k_d,l_d,alx,alx);

    if LHS ne RHS then 
      TF:=false;         
      break cr;
    end if;
  end for;   
  return TF;
end function; 












//calculate u(P), where P is affine cordinate in A^((Z/4Z))^2).
function u_of_ac(ac)
  u:=AssociativeArray();  //wantend.
  for i in set_i do
    for chi in set_chi do
      u[[chi,i]]:=&+[voc[[chi,t]]*ac[ipt[[i,t]]]:t in set_t];
    end for;
  end for;
  return u;
end function;




//inverse function for above function.
//i.e. from u to affine cordinate.
function u_to_ac(u)
  ac:=AssociativeArray();
  for i in set_i do
    ac[i]:=(1/4)*(&+[u[[chi,i]]:chi in set_chi]);
  end for;
  return ac;
end function;









/*

//alnp=an affine lift of null point.
//alx=an of affine lift of x.
//aly=an of affine lift of y.
//alxmy=an of affine lift of x-y.

//we calculate of u_zeta(x+y) from other u.
function calc_uxpy(u0,ux,uy,uxmy,zetas)
  sum:=0;
  for etaa in set_zeta do
    zeta1:=zetas[1];
    ind_1:=precomp_for_add[[zeta1,etaa]][1];  
    ind_2:=precomp_for_add[[zeta1,etaa]][2];  
    ind_3:=precomp_for_add[[zeta1,etaa]][3];   
    ind_4:=precomp_for_add[[zeta1,etaa]][4];

    coff :=precomp_for_add[[zeta1,etaa]][5];    

    sum:=sum+(coff*uy[ind_1]*uy[ind_2]*ux[ind_3]*ux[ind_4]);
  end for;
  return sum/(16*uxmy[zetas[2]]*u0[zetas[3]]*u0[zetas[4]]);
end function;
*/




//alnp=an affine lift of null point.
//alx=an of affine lift of x.
//aly=an of affine lift of y.
//alxmy=an of affine lift of x-y.

//we calculate of u_zeta(x+y) from other u.
function calc_uxpy_2(u0,ux,uy,uxmy,zetas)
  sum:=0;
  for etaa in set_zeta do
    zeta1:=zetas[1];
    ind_1:=precomp_for_add_2[zetas][etaa][1]; 
    ind_2:=precomp_for_add_2[zetas][etaa][2]; 
    ind_3:=precomp_for_add_2[zetas][etaa][3]; 
    ind_4:=precomp_for_add_2[zetas][etaa][4]; 

    coff :=precomp_for_add_2[zetas][etaa][5];     

    sum:=sum+(coff*uy[ind_1]*uy[ind_2]*ux[ind_3]*ux[ind_4]);
  end for;
  return sum/(16*uxmy[zetas[2]]*u0[zetas[3]]*u0[zetas[4]]);
end function;




/*
zeta1:=Random(set_zeta);
zetas:=Random(sub_RP_zeta_Ass[zeta1]);
etaa:=Random(set_zeta);
precomp_for_add[<zetas,etaa>];
precomp_for_add[<zetas,etaa>][1];
*/




//different add.
function add(alnp,alx,aly,alxmy)

  u0:=u_of_ac(alnp);
  ux:=u_of_ac(alx);
  uy:=u_of_ac(aly);
  uxmy:=u_of_ac(alxmy);
  uxpy:=AssociativeArray();

  for zeta1 in set_zeta do
    zetas:=Ass_better_RP_zetas[zeta1];

    assert(u0[zetas[2]] ne 0);  //不要だけど成り立つ仮定.
    assert(u0[zetas[3]] ne 0);   //必要で成り立つ仮定.
    assert(u0[zetas[4]] ne 0);  //必要で成り立つ仮定.
    assert(uxmy[zetas[2]] ne 0);  //必要だけど勝手に仮定.

    uxpy[zeta1]:=pm_for_zeta1[zeta1]*calc_uxpy_2(u0,ux,uy,uxmy,zetas);
  end for;

  assert(Keys(uxpy) eq set_zeta);

  alxpy:=u_to_ac(uxpy);
  return alxpy;
end function;



//for ex_add.
function calc_u_xpypz(u0,ux,uy,uz,uxpy,uxpz,uypz,zetas)
  sum:=0;
  for etaa in set_zeta do
    zeta1:=zetas[1];
    ind_1:=precomp_for_ex_add[zetas][etaa][1]; 
    ind_2:=precomp_for_ex_add[zetas][etaa][2]; 
    ind_3:=precomp_for_ex_add[zetas][etaa][3]; 
    ind_4:=precomp_for_ex_add[zetas][etaa][4]; 
    coff :=precomp_for_add_2[zetas][etaa][5];     
    sum:=sum+(coff*u0[ind_1]*uypz[ind_2]*uxpz[ind_3]*uxpy[ind_4]);
  end for;
  return sum/(16*ux[zetas[2]]*uy[zetas[3]]*uz[zetas[4]]);
end function;





//extended differential addition.
function calc_xpypz(tnp,x,y,z,xpy,xpz,ypz)
               
  u0:=u_of_ac(tnp);
  ux:=u_of_ac(x);
  uy:=u_of_ac(y);
  uz:=u_of_ac(z);
  uxpy:=u_of_ac(xpy);
  uxpz:=u_of_ac(xpz);
  uypz:=u_of_ac(ypz);
  uxpypz:=AssociativeArray();

  for zeta1 in set_zeta do
    zetas:=Ass_better_RP_zetas[zeta1];

    assert(ux[zetas[2]] ne 0);   
    assert(uy[zetas[3]] ne 0);  
    assert(uz[zetas[4]] ne 0);  

    uxpypz[zeta1]:=pm_for_zeta1[zeta1]*calc_u_xpypz(u0,ux,uy,uz,uxpy,uxpz,uypz,zetas);
  end for;

  assert(Keys(uxpy) eq set_zeta);

  xpypz:=u_to_ac(uxpypz);
  return xpypz;
end function;




//calculate k-mult.
function mult(alnp,k,alx)
  assert (k ge 0);
  if (k eq 0) then  //k=0.
    return alnp;
  elif (k eq 1) then  //k=1.
    return alx;
  else   //k>=2.
    tm1_x:=alx;
    tm2_x:=alnp;
    for t in [2..k] do
      tx:=add(alnp,alx,tm1_x,tm2_x);  //tx
      tm2_x:=tm1_x;  //(t-2)x
      tm1_x:=tx;  //(t-1)x
    end for;
    return tx;
  end if;
end function;



//calculate kx+y.
function mult_add(alnp,k,xpy,x,y)
  assert (k ge 0);
  if (k eq 0) then  //k=0.
    return y;
  elif (k eq 1) then  //k=1.
    return xpy;
  else   //k>=2.
    tm1xpy:=xpy;
    tm2xpy:=y;
    for t in [2..k] do
      txpy:=add(alnp,tm1xpy,x,tm2xpy);
      tm2xpy:=tm1xpy;
      tm1xpy:=txpy;
    end for;
    return txpy;
  end if;
end function;









//from e_1,e_2,e_1+e_2, we compute s_1*e_1+s_2*e_2.
function linear_combination(tnp,l,tc1,tc2,tc1p2)
  lin_com:=AssociativeArray();

  lin_com[[0,0]]:=tnp;
  lin_com[[1,0]]:=tc1;
  lin_com[[0,1]]:=tc2;
  lin_com[[1,1]]:=tc1p2;

  for s_1 in [2..l] do
    lin_com[[s_1,0]]:=add(tnp,lin_com[[(s_1-1),0]],lin_com[[1,0]],lin_com[[(s_1-2),0]]);
  end for;

  for s_1 in [2..l] do
    lin_com[[s_1,1]]:=add(tnp,lin_com[[(s_1-1),1]],lin_com[[1,0]],lin_com[[(s_1-2),1]]);
  end for;
  
  for s_1 in [0..l] do
    for s_2 in [2..l] do
      lin_com[[s_1,s_2]]:=add(tnp,lin_com[[s_1,(s_2-1)]],lin_com[[0,1]],lin_com[[s_1,(s_2-2)]]);
    end for;
  end for;

  return lin_com;
end function;







//give x+s_1*e_1+s_2*e_2 for s_1,s_2.
function x_plus_lincom(tnp,l,e_1,e_2,e_1pe_2,x,xpe_1,xpe_2)
  xplin_com:=AssociativeArray();

  xplin_com[[0,0]]:=x;
  xplin_com[[1,0]]:=xpe_1;
  xplin_com[[0,1]]:=xpe_2;
  xplin_com[[1,1]]:=calc_xpypz(tnp,x,e_1,e_2,xpe_1,xpe_2,e_1pe_2);

  //x+s_1*e_1=s_1*x+e_1.
  for s_1 in [2..l] do
    xplin_com[[s_1,0]]:= mult_add(tnp,s_1,xpe_1,e_1,x);
  end for;

  //x+s_1*e_1+e_2=(x+(s_1-1)*e_1+e_2)+e_1.
  for s_1 in [2..l] do
    xplin_com[[s_1,1]]:=add(tnp,xplin_com[[(s_1-1),1]],e_1,xplin_com[[(s_1-2),1]]);
  end for;
  
  for s_1 in [0..l] do
    //x+s_1*e_1+s_2*e_2=(x+s_1*e_1+(s_2-1)*e_2)+e_2.
    for s_2 in [2..l] do
      xplin_com[[s_1,s_2]]:=add(tnp,xplin_com[[s_1,(s_2-1)]],e_2,xplin_com[[s_1,(s_2-2)]]);
    end for;
  end for;

  return xplin_com;
end function;







//linear combination of x,e_1,e_2.
function lincom_xe1e2_new(lincom_e1e2,lv4tnp,l,n,tc_e1,tc_e2,tc_e1pe2,tc_x,tc_xpe1,tc_xpe2)
  
  x_lincom_e1e2:=x_plus_lincom(lv4tnp,l,tc_e1,tc_e2,tc_e1pe2,tc_x,tc_xpe1,tc_xpe2);
  lin_com:=AssociativeArray();

  for s_1 in [0..l] do
    for s_2 in [0..l] do
      for s_0 in [0..(n-1)] do
        //s0*x+s1*e1+s2*e2=s0*x+(s1*e1+s2*e2).
        lin_com[[s_0,s_1,s_2]]:=mult_add(lv4tnp,s_0,x_lincom_e1e2[[s_1,s_2]],tc_x,lincom_e1e2[[s_1,s_2]]);
      end for;
    end for;
  end for;
  return lin_com;
end function;






//End of additions6.m
//============================
