//=====================================
//Start of elliptic_theta3.m



//About elliptic curve---------------------

//from lmd to one of level(2,2)theta null point usign Thomae.
//E: y^2=x(x-1)(x-lmd).
function lmd_to_lv22tnp(lmd)
  _<x>:=PolynomialRing(Parent(lmd));
  E:=EllipticCurve(x*(x-1)*(x-lmd));
  j:=jInvariant(E);
  lv22tnp:=AssociativeArray();
  lv22tnp[[0,0]]:=1;  
  lv22tnp[[0,1]]:=RootsInSplittingField(x^4-(1-1/lmd))[1][1];
  lv22tnp[[1,0]]:=RootsInSplittingField(x^4-1/lmd)[1][1];
  lv22tnp[[1,1]]:=0;
  assert(lv22tnp[[0,0]]^4 eq lv22tnp[[0,1]]^4+lv22tnp[[1,0]]^4);
  lv4tnp:=dim1_lv22tc_to_lv4tc(lv22tnp);
  isss:=IsSupersingular(E);
  return lmd,lv22tnp,lv4tnp,E,j,isss;
end function;




//inverse function of the above.
function lv22tnp_to_lmd(lv22tnp)
  assert (Keys(lv22tnp)eq {[0,0],[0,1],[1,0],[1,1]});
  lmd:=(lv22tnp[[0,0]]/lv22tnp[[1,0]])^4;
  _,lv22tnp_new,lv4tnp,E,j,isss:=lmd_to_lv22tnp(lmd);
  return lmd,lv22tnp_new,lv4tnp,E,j,isss;
end function;



function same_theta_lmd(lmd,lmd_1)
  if lmd_1 in {lmd,1/lmd,1-lmd,1/(1-lmd),1-(1/lmd),lmd/(lmd-1)} then
    return true;
  else 
    return false;
  end if;
end function;







//E translate to the form y^2=x(x-1)(x-lmd).
function E_to_lmd(E)
  bf:=BaseField(E);
  //E:y^2=x^3+ax^2+bx+c;
  a:=bf!Coefficients(E)[2];
  b:=bf!Coefficients(E)[4];
  c:=bf!Coefficients(E)[5];
  _<x>:=PolynomialRing(bf);
  f:=x^3+a*x^2+b*x+c;
  roots:=RootsInSplittingField(f);
  x1:=roots[1][1];
  x2:=roots[2][1];
  x3:=roots[3][1];
  lmd:=(x3-x1)/(x2-x1);
  _,lv22tnp,lv4tnp,E_new,j_new,isss:=lmd_to_lv22tnp(lmd);
  assert(j_new eq jInvariant(E));
  assert(IsIsomorphic(E,E_new));
  _,iso_E_Enew:=IsIsomorphic(E,E_new);
  return lmd,lv22tnp,lv4tnp,E_new,j_new,isss,iso_E_Enew;
end function;




function Is_tnp_dim1(tnp)
  if Keys(tnp) eq {[0],[1],[2],[3]} then
    tnp:=dim1_lv4tc_to_lv22tc(tnp);
  end if;
  assert(Keys(tnp) eq {[0,0],[0,1],[1,0],[1,1]});
  TF1:=(tnp[[1,1]] eq 0);
  TF2:=(tnp[[0,0]]^4 eq tnp[[0,1]]^4+tnp[[1,0]]^4);
  return TF1 and TF2;
end function;





//For point--------------------------------


function Is_on_theta(lv22tnp,lv22tc)
  c:=0;
  //(3.27).
  if (lv22tnp[[0,0]]^2*lv22tc[[0,0]]^2) eq 
  (lv22tnp[[0,1]]^2*lv22tc[[0,1]]^2+lv22tnp[[1,0]]^2*lv22tc[[1,0]]^2) then c+:=1; else "(3.27) is false."; end if;
  //(3.28).
  if (lv22tnp[[0,0]]^2*lv22tc[[1,1]]^2) eq 
  (lv22tnp[[1,0]]^2*lv22tc[[0,1]]^2-lv22tnp[[0,1]]^2*lv22tc[[1,0]]^2) then c+:=1; else "(3.28) is false."; end if;
  //(3.30).
  if (lv22tnp[[0,0]]^2*lv22tc[[0,1]]^2) eq 
  (lv22tnp[[0,1]]^2*lv22tc[[0,0]]^2+lv22tnp[[1,0]]^2*lv22tc[[1,1]]^2) then c+:=1; else "(3.30) is false."; end if;
  if c eq 3 then return true;
  else return false; end if;
end function;







//完成版.
function uv_to_lv4tc(lmd,lv22tnp,u,v)
  assert(v^2 eq u*(u-1)*(u-lmd));
  lv22tc:=AssociativeArray();
  lv22tc[[0,0]]:=lv22tnp[[0,0]]*(u^2-2*u+lmd);
  lv22tc[[0,1]]:=lv22tnp[[0,1]]*(u^2-lmd);
  lv22tc[[1,0]]:=lv22tnp[[1,0]]*(u^2-2*lmd*u+lmd);
  lv22tc[[1,1]]:=(2*v*lv22tnp[[0,1]]*lv22tnp[[0,0]])/lv22tnp[[1,0]];
  assert(Is_on_theta(lv22tnp,lv22tc));
  //u_1,v_1:=lv22tc_to_uv(lmd,lv22tnp,lv22tc);
  //assert(u_1 eq u);
  //assert(v_1 eq v);
  lv4tc:=dim1_lv22tc_to_lv4tc(lv22tc);
  return lv4tc;
end function;







//上の逆関数.
function lv22tc_to_uv(lmd,lv22tnp,lv22tc)
  assert(Is_tnp_dim1(lv22tnp));
  _,lv22tnp_2:=lmd_to_lv22tnp(lmd);
  assert(eq_tc_dim1(lv22tnp,lv22tnp_2));
  assert(Is_on_theta(lv22tnp,lv22tc));

  LHS:=(lv22tc[[0,1]]/lv22tnp[[0,1]])-lmd*(lv22tc[[0,1]]/lv22tnp[[0,1]])+lmd*(lv22tc[[0,0]]/lv22tnp[[0,0]])-(lv22tc[[1,0]]/lv22tnp[[1,0]]);
  mu:=LHS/(2*lmd^2-2*lmd);
  u:=lmd+(lv22tc[[0,1]])/(2*mu*lv22tnp[[0,1]])-(lv22tc[[0,0]])/(2*mu*lv22tnp[[0,0]]);
  v:=(lv22tnp[[1,0]]*lv22tc[[1,1]])/(2*mu*lv22tnp[[0,0]]*lv22tnp[[0,1]]);
  assert(v^2 eq u*(u-1)*(u-lmd));
  return u,v;
end function;








  //lv22tc_2:=dim1_lv4tc_to_lv22tc((uv_to_lv4tc(lmd,lv22tnp,u,v)));
  //eq_Assoc(lv22tc_2,lv22tc);
  return u,v;
end function;











//other functions---------------------------



//g=1でのRiemann positionを準備.
RP_dim1:={};
for ijklm in CartesianPower({0,1,2,3},5) do
  i:=ijklm[1];
  j:=ijklm[2];
  k:=ijklm[3];
  l:=ijklm[4];
  m:=ijklm[5];
  if (i+j+k+l-2*m mod 4) eq 0 then
    i_d:=(m-i) mod 4;
    j_d:=(m-j) mod 4;
    k_d:=(m-k) mod 4;
    l_d:=(m-l) mod 4;
    RP_dim1 join:={[i,j,k,l,i_d,j_d,k_d,l_d]};
  end if;
end for;



function term_dim1(chi,i,j,lv4tc_dim1_1,lv4tc_dim1_2)
  sum:=0;
  for t in {0,1} do
    chi_t:=(-1)^(chi*t);
    ipt:=(i+2*t) mod 4;
    jpt:=(j+2*t) mod 4;
    sum+:=chi_t*lv4tc_dim1_1[[ipt]]*lv4tc_dim1_2[[jpt]];
  end for;
  return sum;
end function;





function Riemann_Relation_dim1(A)
  c:=0;
  for chi in {0,1} do
    for RP8 in RP_dim1 do
      LHS:=term_dim1(chi,RP8[1],RP8[2],A[1],A[2])
          *term_dim1(chi,RP8[3],RP8[4],A[3],A[4]);
      RHS:=term_dim1(chi,RP8[5],RP8[6],A[5],A[6])
          *term_dim1(chi,RP8[7],RP8[8],A[7],A[8]);
      if LHS eq RHS then
        c+:=1;
      end if;
    end for;
  end for;
  if c eq 44 then
    return true;
  else 
    return false;
  end if;
end function;





function Riemann_Relation_dim1_pf(A,mL)
  assert(Keys(A[1]) eq lv4keys_dim1);
  c:=0;
  for chi in {0,1} do
    for RP8 in RP_dim1 do
      LHS:=term_dim1(chi,RP8[1],RP8[2],A[1],A[2])
          *term_dim1(chi,RP8[3],RP8[4],A[3],A[4]);
      RHS:=term_dim1(chi,RP8[5],RP8[6],A[5],A[6])
          *term_dim1(chi,RP8[7],RP8[8],A[7],A[8]);
      if LHS*mL eq RHS then
        c+:=1;
      end if;
    end for;
  end for;
  if c eq 44 then
    return true;
  else 
    return false;
  end if;
end function;





function ell_to_torsion_basis(E,N)
  torsion:=Points(TorsionSubgroupScheme(E,N));
  for P_A in torsion do
    for Q_A in torsion do
      if (Order(P_A) eq N) and (Order(Q_A) eq N) then
        if (#{c_1*P_A+c_2*Q_A: c_1,c_2 in {0..(N-1)}} eq N^2) then
          return P_A,Q_A;
        end if;
      end if;
    end for;
  end for;
end function;
 



function ell_prod_lv4tc(lv4tc1,lv4tc2)
  prod_lv4tc:=AssociativeArray();
  for i in {0..3} do
    for j in {0..3} do
      prod_lv4tc[[i,j]]:=lv4tc1[[i]]*lv4tc2[[j]];
    end for;
  end for;
  assert (Keys(prod_lv4tc) eq lv4keys);
  return prod_lv4tc;
end function;



function ell_prod_lv22tc(lv22tc1,lv22tc2)
  prod_lv22tc:=AssociativeArray();
  for X in {[a1,a2,a3,a4]:a1,a2,a3,a4 in {0,1}} do
    prod_lv22tc[X]:=lv22tc1[[X[1],X[3]]]*lv22tc1[[X[2],X[4]]];
  end for;
  assert (Keys(prod_lv22tc) eq lv22keys);
  return prod_lv22tc;
end function;


//-------------
//theta transformation for g=1.



function kMab_4mult(M,a,b)
  alpha:=M[1];
  beta:=M[2];
  gamma:=M[3];
  delta:=M[4];
  return (delta*a-gamma*b)*(-beta*a+alpha*b+2*alpha*beta)-a*b;
 end function;




function Mab(M,a,b)
  alpha:=M[1];
  beta:=M[2];
  gamma:=M[3];
  delta:=M[4];
  double_Mab_1:=delta*a-gamma*b+gamma*delta;
  double_Mab_2:=-beta*a+alpha*b+alpha*beta;
  return double_Mab_1,double_Mab_2;
end function;






function theta_transform_dim1(lv22tc,M)
  assert(M[1]*M[4]-M[2]*M[3] eq 1);
  _<x>:=PolynomialRing(GF(p));
  zeta_8:=RootsInSplittingField(x^8-1)[2][1];
  assert(zeta_8^4 eq -1);
  tr_lv22tc:=AssociativeArray();

  for ab in {[0,0],[0,1],[1,0],[1,1]} do
    tr_lv22tc_ext:=(zeta_8^kMab_4mult(M,ab[1],ab[1]))*lv22tc[[ab[1],ab[2]]];
    Mab_1,Mab_2:=Mab(M,ab[1],ab[2]);
    a_red,b_red,value:=red_lv22tc_dim1(Mab_1,Mab_2,tr_lv22tc_ext);
    tr_lv22tc[[a_red,b_red]]:=value;
  end for;
  assert(Keys(tr_lv22tc) eq {[0,0],[0,1],[1,0],[1,1]});
  return tr_lv22tc;
end function;






function theta_trans_same4pow(lv22tnp_1,lv22tnp_2)
  for alpha,delta in {-3,-1,1,3,5} do
    for beta,gamma in {-4,-2,0,2,4,6} do
      if alpha*delta-beta*gamma eq 1 then
        M:=[alpha,beta,gamma,delta];
        tr_lv22tnp_1:=theta_transform_dim1(lv22tnp_1,M);
        if eq_tc_dim1(tr_lv22tnp_1,lv22tnp_2) then
          return M;
        end if;
      end if;
    end for;
  end for;
  "Nothing.";
  return false;
end function;











//End of elliptic_theta3.m
//=====================================
