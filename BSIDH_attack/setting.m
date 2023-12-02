/*-----------------------------
you compile the following order.

1st.setting3.m
2nd.func_additions8.m
3rd.func_isogeny3.m
4th.func_elliptic_theta4.m
5th.func_theta_trans.m
6th.func_torsion_attack6.m 
7th.test_setting_attack.m
-----------------------------*/

//=============================================
//Start of setting3.m
//global setting and precomputation.



//---------------------------------------------
//the following "N" gives correspondence between the numbering of [86]A.1.
N:=AssociativeArray();
N[0]:=[0,0,0,0];
N[1]:=[0,0,1,0];
N[2]:=[0,0,0,1];
N[3]:=[0,0,1,1];
N[4]:=[1,0,0,0];
N[5]:=[1,0,1,0];  //odd
N[6]:=[1,0,0,1];
N[7]:=[1,0,1,1];  //odd
N[8]:=[0,1,0,0];
N[9]:=[0,1,1,0];
N[10]:=[0,1,0,1];  //odd
N[11]:=[0,1,1,1];  //odd
N[12]:=[1,1,0,0];
N[13]:=[1,1,1,0];  //odd
N[14]:=[1,1,0,1];  //odd
N[15]:=[1,1,1,1];


//[89]Gaudry-index. 
F:=[];

F[1]:=[0,0,0,0];
F[2]:=[0,0,1,1];
F[3]:=[0,0,1,0];
F[4]:=[0,0,0,1];
F[5]:=[1,0,0,0];
F[6]:=[1,0,0,1];
F[7]:=[0,1,0,0];
F[8]:=[1,1,0,0];
F[9]:=[0,1,1,0];
F[10]:=[1,1,1,1];
//follows odd
F[11]:=[0,1,0,1];
F[12]:=[0,1,1,1];
F[13]:=[1,0,1,0];
F[14]:=[1,1,1,0];
F[15]:=[1,0,1,1];
F[16]:=[1,1,0,1];




//sage order.
S:=AssociativeArray();
S[0]:=[0,0,0,0];
S[1]:=[1,0,0,0];
S[2]:=[0,1,0,0];
S[3]:=[1,1,0,0];
S[4]:=[0,0,1,0];
S[5]:=[1,0,1,0];
S[6]:=[0,1,1,0];
S[7]:=[1,1,1,0];
S[8]:=[0,0,0,1];
S[9]:=[1,0,0,1];
S[10]:=[0,1,0,1];
S[11]:=[1,1,0,1];
S[12]:=[0,0,1,1];
S[13]:=[1,0,1,1];
S[14]:=[0,1,1,1];
S[15]:=[1,1,1,1];

//---------------------------------------------
//you can change any prime p not eq 2.


lv22keys:={[i1,i2,i3,i4]:i1,i2,i3,i4 in {0,1}};
even_lv22keys:={N[index]:index in {0,1,2,3,4,6,8,9,12,15}};
odd_lv22keys:={N[index]:index in {5,7,10,11,13,14}};
lv4keys:={[i,j]:i,j in {0..3}}; 
lv4keys_dim1:={[0],[1],[2],[3]};
lv22keys_dim1:={[0,0],[0,1],[1,0],[1,1]};


//translate theta.------------------------------





function extention_lv22tc(lv22tc)
  //[*,*,2,2].
  for a1 in {0,1} do
    for a2 in {0,1} do
      lv22tc[[a1,a2,0,2]]:=lv22tc[[a1,a2,0,0]]*(-1)^(a2);
      lv22tc[[a1,a2,0,3]]:=lv22tc[[a1,a2,0,1]]*(-1)^(a2);
      lv22tc[[a1,a2,1,2]]:=lv22tc[[a1,a2,1,0]]*(-1)^(a2);
      lv22tc[[a1,a2,1,3]]:=lv22tc[[a1,a2,1,1]]*(-1)^(a2);
      lv22tc[[a1,a2,2,0]]:=lv22tc[[a1,a2,0,0]]*(-1)^(a1);
      lv22tc[[a1,a2,2,1]]:=lv22tc[[a1,a2,0,1]]*(-1)^(a1);
      lv22tc[[a1,a2,2,2]]:=lv22tc[[a1,a2,0,0]]*(-1)^(a1+a2);
      lv22tc[[a1,a2,2,3]]:=lv22tc[[a1,a2,0,1]]*(-1)^(a1+a2);
      lv22tc[[a1,a2,3,0]]:=lv22tc[[a1,a2,1,0]]*(-1)^(a1);
      lv22tc[[a1,a2,3,1]]:=lv22tc[[a1,a2,1,1]]*(-1)^(a1);
      lv22tc[[a1,a2,3,2]]:=lv22tc[[a1,a2,1,0]]*(-1)^(a1+a2);
      lv22tc[[a1,a2,3,3]]:=lv22tc[[a1,a2,1,1]]*(-1)^(a1+a2);
    end for;
  end for;
  return lv22tc;
end function;


function lv22tc_to_lv4tc(lv22tc)
  lv22tc:=extention_lv22tc(lv22tc);
  lv4tc:=AssociativeArray();
  for b1 in {0..3} do
    for b2 in {0..3} do
      lv4tc[[b1,b2]]:=lv22tc[[0,0,b1,b2]]+lv22tc[[0,1,b1,b2]]+lv22tc[[1,0,b1,b2]]+lv22tc[[1,1,b1,b2]];
    end for;
  end for;
  return lv4tc;
end function;




function lv4tc_to_lv22tc(lv4tc)
  lv22tc:=AssociativeArray();
  for a1 in {0,1} do
  for a2 in {0,1} do
  for b1 in {0,1} do
  for b2 in {0,1} do
    lv22tc[[a1,a2,b1,b2]]:=(&+[(-1)^(a1*beta1+a2*beta2)*lv4tc[[(b1+2*beta1)mod 4,(b2+2*beta2)mod 4]]:beta1,beta2 in {0,1}])/4;
  end for;
  end for;
  end for;
  end for;
  return lv22tc;
end function;





function dim1_lv22tc_to_lv4tc(lv22tc)
  lv4tc:=AssociativeArray();
  lv4tc[[0]]:=lv22tc[[0,0]]+lv22tc[[1,0]];
  lv4tc[[1]]:=lv22tc[[0,1]]+lv22tc[[1,1]];
  lv4tc[[2]]:=lv22tc[[0,0]]-lv22tc[[1,0]];
  lv4tc[[3]]:=lv22tc[[0,1]]-lv22tc[[1,1]];
  return lv4tc;
end function;


function dim1_lv4tc_to_lv22tc(lv4tc)
  lv22tc:=AssociativeArray();
  lv22tc[[0,0]]:=(lv4tc[[0]]+lv4tc[[2]])/2;
  lv22tc[[0,1]]:=(lv4tc[[1]]+lv4tc[[3]])/2;
  lv22tc[[1,0]]:=(lv4tc[[0]]-lv4tc[[2]])/2;
  lv22tc[[1,1]]:=(lv4tc[[1]]-lv4tc[[3]])/2;
  return lv22tc;
end function;





function to_lv22(tc)
  if Keys(tc) eq lv22keys then
    return tc;
  elif Keys(tc) eq lv22keys_dim1 then
    return tc;
  elif Keys(tc) eq lv4keys then
    return lv4tc_to_lv22tc(tc);
  elif Keys(tc) eq lv4keys_dim1 then
    return dim1_lv4tc_to_lv22tc(tc);
  else
    "Error.";
    return false;
  end if;
end function;



function to_lv4(tc)
  if Keys(tc) eq lv4keys then
    return tc;
  elif Keys(tc) eq lv4keys_dim1 then
    return tc;
  elif Keys(tc) eq lv22keys then
    return lv22tc_to_lv4tc(tc);
  elif Keys(tc) eq lv22keys_dim1 then
    return dim1_lv22tc_to_lv4tc(tc);
  else
    "Error.";
    return false;
  end if;
end function;








function eq_tc_dim1(tc1,tc2)
  if Keys(tc1) eq lv4keys_dim1 then
    tc1:=dim1_lv4tc_to_lv22tc(tc1);
  end if;
  if Keys(tc2) eq lv4keys_dim1 then
    tc2:=dim1_lv4tc_to_lv22tc(tc2);
  end if;
  const:=tc1[[0,0]]/tc2[[0,0]];
  return forall{key:key in {[0,0],[0,1],[1,0],[1,1]}|tc1[key] eq const*tc2[key]};
end function;





function ext_lv22tc_dim1(lv22tc,a,b)
  a_red:=a mod 2;
  b_red:=b mod 2;
  alpha:=a-a_red;
  beta:=b-b_red;
  semi_beta:=IntegerRing()!(beta/2);
  coff:=(-1)^(a_red*semi_beta);
  return coff*lv22tc[[a_red,b_red]];
end function;



function red_lv22tc_dim1(a,b,lv22tc_ab)
  a_red:=a mod 2;
  b_red:=b mod 2;
  alpha:=a-a_red; //even.
  beta:=b-b_red;  //even.
  semi_beta:=IntegerRing()!(beta/2);
  coff:=(-1)^(a_red*semi_beta);
  return a_red,b_red,coff*lv22tc_ab;
end function;

 





function value_0is1(tc)
  if Keys(tc) eq lv22keys then
    const:=tc[[0,0,0,0]];
  elif Keys(tc) eq lv4keys then
    const:=tc[[0,0]];
  elif Keys(tc) eq {[i]:i in {0..3}} then
    const:=tc[[0]];
  elif Keys(tc) eq {[0,0],[0,1],[1,0],[1,1]} then
    const:=tc[[0,0]];
  else
    "Nothing";
    return false;
  end if;
  for key in Keys(tc) do
    tc[key]:=tc[key]/const;
  end for;
  return tc;
end function;



function inverse_element(lv4tc)
  i_lv4tc:=AssociativeArray();
  for a in {0..3} do
    for b in {0..3} do
      i_lv4tc[[a,b]]:=lv4tc[[(-a) mod 4,(-b) mod 4]];
    end for;
  end for;
  return i_lv4tc;
end function;



//-----------------------




function Is_prod_ell(tnp)
  if Keys(tnp) eq lv4keys then
    tnp:=lv4tc_to_lv22tc(tnp);
  end if;
  if #{key:key in lv22keys|tnp[key] eq 0} gt 6 then
    return true;
  else 
    return false;
  end if;
end function;



function get_characteristic(tc)
  for key in Keys(tc) do
    if IsFinite(Parent(tc[key])) then
      p:=Characteristic(Parent(tc[key]));
      break key;
    end if;
  end for;
  return p;
end function;









//take base field of theta cordinate.
function global_field(tc)
  index_set:={};
  p:=get_characteristic(tc);
  for key in Keys(tc) do
    if IsFinite(Parent(tc[key])) then
      index:=1;
      while #(Parent(tc[key])) ne p^index do
        index+:=1;
      end while;
      index_set join:={index};
    end if;
  end for;
  
  if (#index_set eq 0) then
    assert(false);
  else 
    q:=p^LCM(index_set);
  end if;
  for key in Keys(tc) do
    tc[key]:=GF(q)!tc[key];
  end for;
  return tc,GF(q);
end function;




//take base field of sequence of theta cordinates.
function global_field_of_seq(tc_seq)
  pow_set:={};
  p:=get_characteristic(tc_seq[1]);
  for index in {1..(#tc_seq)} do
    for key in Keys(tc_seq[index]) do
      if IsFinite(Parent(tc_seq[index][key])) then
        pow:=1;
        while #(Parent(tc_seq[index][key])) ne p^pow do
          pow+:=1;
        end while;
        pow_set join:={pow};
      end if;
    end for;
  end for;
  if (#pow_set eq 0) then
    q:=p;
  else 
    q:=p^LCM(pow_set);
  end if;
  for index in {1..(#tc_seq)} do
    for key in Keys(tc_seq[index]) do
      tc_seq[index][key]:=GF(q)!tc_seq[index][key];
    end for;
  end for;
  return tc_seq,GF(q);
end function;



//------------------------------------------
//precomputation about Riemann position.

//for condition g=2,n=4.
set_i:={[i,j]:i,j in {0..3}};
set_chi:={[i,j]:i,j in {0,1}};
set_t:={[i,j]:i,j in {0,1}};
set_zeta:={[chi,i]:chi in set_chi, i in set_i};



//In advance, we calculate value of calculate of (Z/2Z)^2, and store it in "voc".
voc:=AssociativeArray();    
for chi in set_chi do
  for t in set_t do
    voc[[chi,t]]:=(-1)^(chi[1]*t[1]+chi[2]*t[2]);
  end for;
end for;


//we consider i+t as element of seti,and it is weritten by k[[i,t]]. 
ipt:=AssociativeArray();
for i in set_i do
  for t in set_t do
    ipt[[i,t]]:=[((i[1]+2*t[1]) mod 4),((i[2]+2*t[2]) mod 4)];
  end for;
end for;


//Riemann position on (Z/2Z)^2.
RP_chi:={};  // 256/1024.
Candidate_chi:=CartesianPower(set_chi,5);
for CD in Candidate_chi do
  if (((CD[1][1]+CD[2][1]+CD[3][1]+CD[4][1]-2*CD[5][1]) mod 2) eq 0) then 
    if (((CD[1][2]+CD[2][2]+CD[3][2]+CD[4][2]-2*CD[5][2]) mod 2) eq 0) then 
      RP_chi:=RP_chi join {CD};
    end if;
  end if;
end for;



//construct some Riemann position set for i in (Z/4Z)^2. 
//use only Riemann Relation.
sub_RP_i:={};  
for i in set_i do
  for number in {1..300} do
    CD:=Random(CartesianPower(set_i,3));
    CD5:=[];
    CD5[1]:=i;
    CD5[2]:=CD[1];
    CD5[3]:=CD[2];
    CD5[5]:=CD[3];
    CD5[4]:=[((2*CD5[5][1]-(CD5[1][1]+CD5[2][1]+CD5[3][1])) mod 4),((2*CD5[5][2]-(CD5[1][2]+CD5[2][2]+CD5[3][2])) mod 4)];
    sub_RP_i:=sub_RP_i join {CD5};
  end for;
end for;




//zeta s.t. u_zeta(0) ne 0.
//the following set "non0_zeta"  doesnt depend on Ros.
//#u_zeta_tnp_ne0=40/64.

//40/64.
jacob_u0ne0:=
{[[1,1],[1,1]],[[0,0],[3,2]],[[1,1],[1,3]],[[0,0],[3,3]],[[0,0],[3,0]],[[0,0],[3,1]],[[0,1],[2,2]],[[0,1],[2,0]],[[0,0],[2,2]],[[0,0],[2,3]],[[0,0],[2,0]],[[0,0],[2,1]],[[1,1],[2,2]],[[1,1],[2,0]],[[1,0],[0,0]],[[1,1],[3,3]],[[1,0],[0,1]],[[1,0],[0,2]],[[1,1],[3,1]],[[0,0],[1,0]],[[1,0],[0,3]],[[1,0],[2,2]],[[0,0],[1,1]],[[0,0],[1,2]],[[1,0],[2,3]],[[0,0],[1,3]],[[1,0],[2,0]],[[1,0],[2,1]],[[0,1],[0,0]],[[1,1],[0,0]],[[0,1],[0,2]],[[0,1],[1,0]],[[1,1],[0,2]],[[0,1],[1,2]],[[0,0],[0,0]],[[0,0],[0,1]],[[0,0],[0,2]],[[0,0],[0,3]],[[0,1],[3,2]],[[0,1],[3,0]]};


//36/64.
ellprod_u0ne0:=
{[[0,0],[3,2]],[[0,0],[3,3]],[[0,0],[3,0]],[[0,0],[3,1]],[[0,1],[2,2]],[[0,1],[2,0]],[[0,0],[2,2]],[[0,0],[2,3]],[[0,0],[2,0]],[[0,0],[2,1]],[[1,1],[2,2]],[[1,1],[2,0]],[[1,0],[0,0]],[[1,0],[0,1]],[[1,0],[0,2]],[[0,0],[1,0]],[[1,0],[0,3]],[[1,0],[2,2]],[[0,0],[1,1]],[[0,0],[1,2]],[[1,0],[2,3]],[[0,0],[1,3]],[[1,0],[2,0]],[[1,0],[2,1]],[[0,1],[0,0]],[[1,1],[0,0]],[[0,1],[0,2]],[[0,1],[1,0]],[[1,1],[0,2]],[[0,1],[1,2]],[[0,0],[0,0]],[[0,0],[0,1]],[[0,0],[0,2]],[[0,0],[0,3]],[[0,1],[3,2]],[[0,1],[3,0]]};

//32/64.
all_u0ne0:=
{[[0,1],[2,2]],[[0,1],[2,0]],[[0,1],[1,0]],[[0,1],[1,2]],[[1,0],[0,0]],[[1,0],[0,1]],[[1,0],[0,2]],[[1,0],[0,3]],[[0,0],[1,1]],[[0,0],[1,3]],[[0,0],[3,3]],[[1,0],[2,2]],[[1,1],[0,0]],[[0,0],[3,1]],[[1,0],[2,3]],[[1,0],[2,0]],[[1,1],[0,2]],[[1,0],[2,1]],[[1,1],[2,2]],[[0,1],[3,2]],[[0,1],[0,0]],[[1,1],[2,0]],[[0,1],[3,0]],[[0,1],[0,2]]};


RP_zetas:={};
for car_zeta1 in CartesianProduct(set_chi,set_i) do
  zeta1:=[car_zeta1[1],car_zeta1[2]];
  for number in {1..50} do
    zeta3:=Random(all_u0ne0);
    zeta4:=Random(all_u0ne0);
    car_zeta5:=Random(CartesianProduct(set_chi,set_i));
    zeta5:=[car_zeta5[1],car_zeta5[2]];

    chi2:=[(2*zeta5[1][1]-(zeta1[1][1]+zeta3[1][1]+zeta4[1][1])) mod 2,(2*zeta5[1][2]-(zeta1[1][2]+zeta3[1][2]+zeta4[1][2])) mod 2];
    j:=[(2*zeta5[2][1]-(zeta1[2][1]+zeta3[2][1]+zeta4[2][1])) mod 4,
    (2*zeta5[2][2]-(zeta1[2][2]+zeta3[2][2]+zeta4[2][2])) mod 4];

    zeta2:=[chi2,j];
    if zeta2 in all_u0ne0 then
      zetas:=[zeta1,zeta2,zeta3,zeta4,zeta5];
      RP_zetas join:={zetas};
    end if;
  end for;
end for;






//=================================
//precomputation for addition.


function zeta_add(zeta1,zeta2)
  plus_zeta:=[];
  plus_zeta[1]:=[((zeta1[1][1]+zeta2[1][1])mod 2),((zeta1[1][2]+zeta2[1][2])mod 2)];
  plus_zeta[2]:=[((zeta1[2][1]+zeta2[2][1])mod 4),((zeta1[2][2]+zeta2[2][2])mod 4)];
  return plus_zeta;
end function;



function zeta_minus(zeta1,zeta2)
  plus_zeta:=[];
  plus_zeta[1]:=[((zeta1[1][1]-zeta2[1][1])mod 2),((zeta1[1][2]-zeta2[1][2])mod 2)];
  plus_zeta[2]:=[((zeta1[2][1]-zeta2[2][1])mod 4),((zeta1[2][2]-zeta2[2][2])mod 4)];
  return plus_zeta;
end function;






precomp_for_add_3:=AssociativeArray(); 
for zetas in RP_zetas do
  precomp_for_add_3[zetas]:=AssociativeArray();
  for etaa in set_zeta do
    zeta1:=zetas[1];
    zeta2:=zetas[2];
    zeta3:=zetas[3];
    zeta4:=zetas[4];
    eps:=zetas[5];

    omega:=etaa[1];
    h:=etaa[2];
    phi:=eps[1];

    //calculate zeta'.
    zeta1_d:=zeta_minus(eps,zeta1);
    zeta2_d:=zeta_minus(eps,zeta2);
    zeta3_d:=zeta_minus(eps,zeta3);
    zeta4_d:=zeta_minus(eps,zeta4);

    phi_plus_omega:=[((phi[1]+omega[1]) mod 2),((phi[2]+omega[2]) mod 2)];
    double_h:=[(h[1] mod 2),(h[2] mod 2)];
    coff:=(-1)^(phi_plus_omega[1]*double_h[1]+phi_plus_omega[2]*double_h[2]);

    ind_zeta1:=zeta_minus(zeta1_d,etaa);  //remark.
    ind_zeta2:=zeta_minus(etaa,zeta2_d);
    ind_zeta3:=zeta_minus(etaa,zeta3_d);
    ind_zeta4:=zeta_minus(etaa,zeta4_d);
  
    precomp_for_add_3[zetas][etaa]
    :=<ind_zeta1,ind_zeta2,ind_zeta3,ind_zeta4,coff>;
  end for;
end for;





//precomputation for "extended diff add".
precomp_for_ex_add_2:=AssociativeArray(); 
for zetas in RP_zetas do
  precomp_for_ex_add_2[zetas]:=AssociativeArray();
  for etaa in set_zeta do
    zeta1:=zetas[1];
    zeta2:=zetas[2];
    zeta3:=zetas[3];
    zeta4:=zetas[4];
    eps:=zetas[5];
    omega:=etaa[1];
    h:=etaa[2];
    phi:=eps[1];
    //calculate zeta'.
    zeta1_d:=zeta_minus(eps,zeta1);
    zeta2_d:=zeta_minus(eps,zeta2);
    zeta3_d:=zeta_minus(eps,zeta3);
    zeta4_d:=zeta_minus(eps,zeta4);
    phi_plus_omega:=[((phi[1]+omega[1]) mod 2),((phi[2]+omega[2]) mod 2)];
    double_h:=[(h[1] mod 2),(h[2] mod 2)];
    coff:=(-1)^(phi_plus_omega[1]*double_h[1]+phi_plus_omega[2]*double_h[2]);
    ind_zeta1:=zeta_minus(etaa,zeta1_d);
    ind_zeta2:=zeta_minus(etaa,zeta2_d);
    ind_zeta3:=zeta_minus(etaa,zeta3_d);
    ind_zeta4:=zeta_minus(etaa,zeta4_d);
    precomp_for_ex_add_2[zetas][etaa]
    :=<ind_zeta1,ind_zeta2,ind_zeta3,ind_zeta4,coff>;
  end for;
end for;






sign_of_zeta1:=AssociativeArray();
for zeta1 in set_zeta do
  if zeta1 in jacob_u0ne0 then
    sign_of_zeta1[zeta1]:=1;
  else 
    sign_of_zeta1[zeta1]:=-1;
  end if;
end for;
assert (Keys(sign_of_zeta1) eq set_zeta);



//------------------------------

sign_jacob:=AssociativeArray();
for zeta1 in set_zeta do
  if zeta1 in jacob_u0ne0 then
    sign_jacob[zeta1]:=1;
  else 
    sign_jacob[zeta1]:=-1;
  end if;
end for;
assert (Keys(sign_jacob) eq set_zeta);
//--------------------------





//_______________________________
//construct a set Pow(S) from S.

function TakePow(S)
  L:=Setseq(S);
  n:=#S;
  Pow:={};
  for bit in CartesianPower({0,1},n) do
    T:={};
    for k in [1..n] do
      if bit[k] eq 1 then
        T:=T join {L[k]};
      end if;
    end for;
    Pow:=Pow join {T};
  end for;
  return Pow;
end function; 



//---------------------------------------------
//construct eta.

Powset:=TakePow({0,1,2,3,4,5});
U:={1,3,5};

eta1:=AssociativeArray();

eta1[0]:=[0,0,0,0];  //infty.
eta1[1]:=[1,0,0,0];
eta1[2]:=[1,0,1,0];
eta1[3]:=[0,1,1,0];
eta1[4]:=[0,1,1,1];
eta1[5]:=[0,0,1,1];

Powset:=TakePow({0,1,2,3,4,5});

eta:=AssociativeArray();

for ss in Powset do  
  if #ss ne 0 then 
    eta[ss]:=[];
    for index in {1..4} do
      eta[ss][index]:=((&+[eta1[num][index]:num in ss]) mod 2);
    end for;
  end if;
  eta[{}]:=[0,0,0,0];
end for;


 
//construct inverse func of the above.
inveta:=AssociativeArray();

for A in TakePow({1..5}) do
  if #A le 2 then 
    inveta[eta[A]]:=A;
  end if;
end for;



//for given [,,,], give even B s.t. t_B=f_B*theta[,,].
give_index_tf:=AssociativeArray();
U:={1,3,5};
for B in TakePow({1..5}) do
  if #B eq 1 then
    give_index_tf[eta[U sdiff B]]:=B;
  end if;
  if (#B eq 0 or #B eq 2) then 
    A:={1..5} diff B;
    give_index_tf[eta[U sdiff A]]:=B;
  end if;
end for;

give_index_tf:=AssociativeArray();
U:={1,3,5};
for B in TakePow({1..5}) do
  if #B eq 1 then
    give_index_tf[eta[U sdiff B]]:=B;
  end if;
  if (#B eq 0 or #B eq 2) then 
    A:={1..5} diff B;
    give_index_tf[eta[U sdiff A]]:=B;
  end if;
end for;


get_A:=AssociativeArray();
U:={1,3,5};
for A in TakePow({1..5}) do
  if (#A le 2) then
    get_A[eta[U sdiff A]]:=A;
  end if;
end for;



//---------------------------------------------
//e.g. key=[2,0,1,2].
function moduloZ(key) 
  new_key:=[];
  Zk:=[];
  for index in [1..4] do
    if key[index] eq 2 then 
      new_key[index]:=0;
      Zk[index]:=1;
    else 
      new_key[index]:=key[index];
      Zk[index]:=0;
    end if;
  end for;
  sign:=(-1)^(new_key[1]*Zk[3]+new_key[2]*Zk[4]);
  return new_key,sign;
end function;



index_set:=AssociativeArray();
sign_set:=AssociativeArray();

for ab in odd_lv22keys do
  for albe in lv22keys do
    index_set[[ab,albe]]:={
      [(ab[1]+albe[1])mod 2,(ab[2]+albe[2])mod 2,(ab[3]+albe[3])mod 2,(ab[4]+albe[4])mod 2],
      [(ab[1]+albe[1])mod 2,(ab[2]+albe[2])mod 2,(albe[3])mod 2,(albe[4])mod 2],
      [(albe[1])mod 2,(albe[2])mod 2,(ab[3]+albe[3])mod 2,(ab[4]+albe[4])mod 2],
      albe};

    _,s1:=moduloZ([ab[1]+albe[1],ab[2]+albe[2],ab[3]+albe[3],ab[4]+albe[4]]);
    _,s2:=moduloZ([ab[1]+albe[1],ab[2]+albe[2],albe[3],albe[4]]);//1
    _,s3:=moduloZ([albe[1],albe[2],ab[3]+albe[3],ab[4]+albe[4]]);
    _,s4:=moduloZ(albe);//1

    sign_set[[ab,albe]]:=((-1)^(ab[1]*albe[3]+ab[2]*albe[4]))*s1*s2*s3*s4;
  end for;
end for;


pre_data_of_ab:=AssociativeArray();
for ab in odd_lv22keys do
  pre_data_of_ab[ab]:=AssociativeArray();
  for albe in lv22keys do
    pre_data_of_ab[ab][albe]:=
    <ab,
    {index_set[[ab,albe]] : albe in lv22keys},
    {give_index_tf[key]:key in index_set[[ab,albe]]},
    sign_set[[ab,albe]]>;
  end for;
end for;


data_of_ab:=AssociativeArray();
for ab in odd_lv22keys do
  data_of_ab[ab]:={pre_data_of_ab[ab][albe] : albe in lv22keys};
end for;


//---------------------------------------------
//reparesentation procedure of theta cordinate.

procedure lv22rep(lv22tc)
  const:=lv22tc[N[0]];
  for index in [0..15] do
    index;
    lv22tc[N[index]]/const;
    "";
  end for;
end procedure;


procedure lv22repsq(lv22tc)
  const:=lv22tc[N[0]];
  for index in [0..15] do
    index;
    (lv22tc[N[index]]/const)^2;
    "";
  end for;
end procedure;



procedure lv4rep(lv4tc)
  const:=lv4tc[[0,0]];
  for index1 in [0..3] do
    for index2 in [0..3] do
      [index1,index2];
      lv4tc[[index1,index2]]/const;
    end for;
  end for;
end procedure;
 


//express theta cordinate. 
procedure expr(tc)
  if Keys(tc) eq lv22keys then
    const:=tc[N[0]];
    for index in [0..15] do
      index;
      tc[N[index]]/const;
      "";
    end for;

  elif Keys(tc) eq lv4keys then
    const:=tc[[0,0]];
    for index1 in [0..3] do
      for index2 in [0..3] do
        [index1,index2];
        tc[[index1,index2]]/const;
      end for;
    end for;
  end if;
end procedure;


//---------------------------------------------

 
//extend the keys of lv(2,2) theta cordinate.
function  ext_chara_lv22(lv22tc)
  ext_lv22tc:=AssociativeArray();
  for chara in {[a1,a2,b1,b2]: a1,a2,b1,b2 in [0..3]} do
    //chara=chara1+(2*chara2). (0<=chara<=1)
    chara1:=[chara[1] mod 2,chara[2] mod 2,chara[3] mod 2,chara[4] mod 2];
    chara2:=[];
    for index in [1..4] do
      chara2[index]:=IntegerRing()!(1/2*(chara[index]-chara1[index]));
    end for;
    sign:=(-1)^(chara1[1]*chara2[3]+chara1[2]*chara2[4]);
    ext_lv22tc[chara]:=sign*lv22tc[chara1];
  end for;
  return ext_lv22tc;
end function;






//-----------------------------------------

//decision if given two Associative array is the same.

function eq_Assoc(A,B)
  assert (Category(A) eq Assoc);
  assert (Category(B) eq Assoc);
  if Keys(A) ne Keys(B) then
    "Keys are different.";
    return false;
  end if;
  if Keys(A) eq Keys(B) then
    for key in Keys(A) do
      if A[key] ne B[key] then 
        return false;
      end if;
    end for;
  end if;
  return true;
end function;





function eq_tc(tc1,tc2)
  assert (Category(tc1) eq Category(tc2));

  if Keys(tc1) eq lv22keys then
    const:=tc1[[0,0,0,0]]/tc2[[0,0,0,0]];
    return forall{key : key in lv22keys |  tc1[key] eq const*tc2[key]};
  end if;

  if Keys(tc1) eq lv4keys then
    const:=tc1[[0,0]]/tc2[[0,0]];
    return forall{key : key in lv4keys |  tc1[key] eq const*tc2[key]};
  end if;

end function;




//---------------------------------------
//precomputation for constructing of 2-torision point.
u_to_z:=AssociativeArray();

u_to_z[{}]:=<0,0,0,0>;

u_to_z[{1}]:=<1,0,0,0>;
u_to_z[{2}]:=<1,0,1,0>;
u_to_z[{3}]:=<0,1,1,0>;
u_to_z[{4}]:=<0,1,1,1>;
u_to_z[{5}]:=<0,0,1,1>;

for i in {1..4} do
  for j in {(i+1)..5} do
    u_to_z[{i,j}]:=
    <((u_to_z[{i}][1]+u_to_z[{j}][1]) mod 2),
    ((u_to_z[{i}][2]+u_to_z[{j}][2]) mod 2),
    ((u_to_z[{i}][3]+u_to_z[{j}][3]) mod 2),
    ((u_to_z[{i}][4]+u_to_z[{j}][4]) mod 2)>;
  end for;
end for;
//---------------------------------------


function minus_lv4tc(lv4tc)
  m_lv4tc:=AssociativeArray(); //wanted.  
  for key in lv4keys do
    newkey:=[-key[1] mod 4, -key[2] mod 4];
    m_lv4tc[newkey]:=lv4tc[key];
  end for;
  return m_lv4tc;
end function;


//----------------------------------

//construct all Rimeann positions in g=1.
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



//End of setting3.m
//===================================================

