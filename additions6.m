
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
  TF:=true; //wanted.
  for cr in CartesianProduct(set_chi,sub_RP_i) do
    i2:=[(cr[2][5][1]-cr[2][1][1]) mod 4,(cr[2][5][2]-cr[2][1][2]) mod 4];
    j2:=[(cr[2][5][1]-cr[2][2][1]) mod 4,(cr[2][5][2]-cr[2][2][2]) mod 4];
    k2:=[(cr[2][5][1]-cr[2][3][1]) mod 4,(cr[2][5][2]-cr[2][3][2]) mod 4];
    l2:=[(cr[2][5][1]-cr[2][4][1]) mod 4,(cr[2][5][2]-cr[2][4][2]) mod 4];

    LHS:=term(cr[1],cr[2][1],cr[2][2],A[1],A[2])*term(cr[1],cr[2][3],cr[2][4],A[3],A[4]);

    RHS:=term(cr[1],i2,j2,A[5],A[6])*term(cr[1],k2,l2,A[7],A[8]);

    if LHS ne RHS then 
      TF:=false;         
      break cr;
    end if;
  end for;   
  return TF;
end function; 



//this function gives only necessary condition.
function Is_lv4tnp(lv4tnp)
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

    uxpy[zeta1]:=pm_for_zeta1[zeta1]*calc_uxpy(u0,ux,uy,uxmy,zetas);
  end for;

  assert(Keys(uxpy) eq set_zeta);

  alxpy:=u_to_ac(uxpy);
  return alxpy;
end function;





//calculate k-mult.
function mult(alnp,k,alx)
  assert (k gt 0);

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


//End of additions6.m
//============================
