/*-----------------------------
you compile the following order.

1st.setting.m
2nd.Mum_to_theta7.m
3rd.additions6.m
4th.isogeny.m
-----------------------------*/

//========================================================
//Start of setting.m
//global setting and precomputation.

p:=11;

q:=p^2;
K<z>:=GF(q);
L:=GF(q^2);
Kx<x>:=PolynomialRing(GF(p));

PM10:=<1, 1, -1, 1, 1, 1, -1, 1, -1, -1>;



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



//[89]Gaudry-index. the same with Ohashi's. 
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











//---------------------------------------------
//you can change any prime p not eq 2.

n:=4;
g:=2;

l:=5;    
//F:=Matrix([[1, 2],[-2,1]]);  //F depends on l=5. here 5=1^2+2^2 so r=2.
r:=2;

lv22keys:={[i1,i2,i3,i4]:i1,i2,i3,i4 in {0,1}};
even_lv22keys:={N[index]:index in {0,1,2,3,4,6,8,9,12,15}};
odd_lv22keys:={N[index]:index in {5,7,10,11,13,14}};
lv4keys:={[i,j]:i,j in {0..3}}; 


//=======================
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



/*
//Riemann position on (Z/4Z)^2.
RP_i:={};  // 65536/(2^20). 6%//take 5min.
Candidate_i:=CartesianPower(set_i,5);
for CD in Candidate_i do
  if (((CD[1][1]+CD[2][1]+CD[3][1]+CD[4][1]-2*CD[5][1]) mod 4) eq 0) then 
    if (((CD[1][2]+CD[2][2]+CD[3][2]+CD[4][2]-2*CD[5][2]) mod 4) eq 0) then 
      RP_i:=RP_i join {CD};
    end if;
  end if;
end for;
*/



//set_iのRiemann_positionの組をいくつかランダム生成.
sub_RP_i:={};  
later4_Candidate_i:=CartesianPower(set_i,3);
sub_Candidate_i:={};

for i in set_i do
  for number in {1..10} do
    CD:=Random(later4_Candidate_i);
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
u_zeta_tnp_ne0:=
{[[1,1],[1,1]],[[0,0],[3,2]],[[1,1],[1,3]],[[0,0],[3,3]],[[0,0],[3,0]],[[0,0],[3,1]],[[0,1],[2,2]],[[0,1],[2,0]],[[0,0],[2,2]],[[0,0],[2,3]],[[0,0],[2,0]],[[0,0],[2,1]],[[1,1],[2,2]],[[1,1],[2,0]],[[1,0],[0,0]],[[1,1],[3,3]],[[1,0],[0,1]],[[1,0],[0,2]],[[1,1],[3,1]],[[0,0],[1,0]],[[1,0],[0,3]],[[1,0],[2,2]],[[0,0],[1,1]],[[0,0],[1,2]],[[1,0],[2,3]],[[0,0],[1,3]],[[1,0],[2,0]],[[1,0],[2,1]],[[0,1],[0,0]],[[1,1],[0,0]],[[0,1],[0,2]],[[0,1],[1,0]],[[1,1],[0,2]],[[0,1],[1,2]],[[0,0],[0,0]],[[0,0],[0,1]],[[0,0],[0,2]],[[0,0],[0,3]],[[0,1],[3,2]],[[0,1],[3,0]]};



/*
sub_RP_zeta:={};    
for zeta_1 in CartesianProduct(set_chi,set_i) do
  zeta1:=[zeta_1[1],zeta_1[2]];
  c:=0;
  while (c lt 1) do  //1個ランダムに生成.
    //const 10 zeta s.t. zeta[1]=zeta_1.
    zeta3:=Random(u_zeta_tnp_ne0);
    zeta4:=Random(u_zeta_tnp_ne0);
    zeta_5:=Random(CartesianProduct(set_chi,set_i));
    zeta5:=[zeta_5[1],zeta_5[2]];
  
    chi2:=[(2*zeta5[1][1]-(zeta1[1][1]+zeta3[1][1]+zeta4[1][1])) mod 2,(2*zeta5[1][2]-(zeta1[1][2]+zeta3[1][2]+zeta4[1][2])) mod 2];
    j:=[(2*zeta5[2][1]-(zeta1[2][1]+zeta3[2][1]+zeta4[2][1])) mod 4,(2*zeta5[2][2]-(zeta1[2][2]+zeta3[2][2]+zeta4[2][2])) mod 4];
    zeta2:=[chi2,j];

    if zeta2 in u_zeta_tnp_ne0 then
      sub_RP_zeta:=sub_RP_zeta join {[zeta1,zeta2,zeta3,zeta4,zeta5]};
      c:=c+1;
    end if;
  end while;
end for;
*/

/*
set_better_RP_zetas:={};
for zeta_1 in CartesianProduct(set_chi,set_i) do
  zeta1:=[zeta_1[1],zeta_1[2]];
  c:=0;
  while (c lt 1) do  //1個ランダムに生成.
    //const 10 zeta s.t. zeta[1]=zeta_1.
    zeta3:=Random(u_zeta_tnp_ne0);
    zeta4:=Random(u_zeta_tnp_ne0);
    zeta_5:=Random(CartesianProduct(set_chi,set_i));
    zeta5:=[zeta_5[1],zeta_5[2]];
  
    chi2:=[(2*zeta5[1][1]-(zeta1[1][1]+zeta3[1][1]+zeta4[1][1])) mod 2,(2*zeta5[1][2]-(zeta1[1][2]+zeta3[1][2]+zeta4[1][2])) mod 2];
    j:=[(2*zeta5[2][1]-(zeta1[2][1]+zeta3[2][1]+zeta4[2][1])) mod 4,(2*zeta5[2][2]-(zeta1[2][2]+zeta3[2][2]+zeta4[2][2])) mod 4];
    zeta2:=[chi2,j];

    if zeta2 in u_zeta_tnp_ne0 then
      zetas:=[zeta1,zeta2,zeta3,zeta4,zeta5];
      set_better_RP_zetas:=set_better_RP_zetas join {zetas};
      c:=c+1;
    end if;
  end while;
end for;
assert (#set_better_RP_zetas eq 64);
*/

//the following set is constructed by the above for-roop.

set_better_RP_zetas:=
  {[[[ 0, 1 ],[ 3, 2 ]],[[ 0, 1 ],[ 3, 0 ]],[[ 1, 1 ],[ 2, 2 ]],[[ 1, 1 ],[ 0, 0 ]],[[ 0, 1 ],[ 2, 2 ]]],[[[ 1, 1 ],[ 0, 3 ]],[[ 1, 1 ],[ 3, 3 ]],[[ 0, 0 ],[ 0, 0 ]],[[ 0, 0 ],[ 1, 2 ]],[[ 1, 0 ],[ 2, 2 ]]],[[[ 0, 0 ],[ 1, 0 ]],[[ 0, 0 ],[ 0, 3 ]],[[ 1, 1 ],[ 3, 1 ]],[[ 1, 1 ],[ 2, 2 ]],[[ 1, 0 ],[ 1, 3 ]]],[[[ 0, 0 ],[ 3, 3 ]],[[ 0, 1 ],[ 0, 0 ]],[[ 0, 0 ],[ 2, 1 ]],[[ 0, 1 ],[ 1, 2 ]],[[ 0, 0 ],[ 1, 1 ]]],[[[ 1, 0 ],[ 3, 2 ]],[[ 1, 1 ],[ 0, 2 ]],[[ 0, 1 ],[ 1, 0 ]],[[ 0, 0 ],[ 0, 0 ]],[[ 0, 1 ],[ 0, 2 ]]],[[[ 0, 1 ],[ 1, 1 ]],[[ 1, 0 ],[ 2, 2 ]],[[ 1, 0 ],[ 0, 1 ]],[[ 0, 1 ],[ 1, 0 ]],[[ 1, 0 ],[ 2, 0 ]]],[[[ 1, 0 ],[ 1, 3 ]],[[ 1, 0 ],[ 0, 3 ]],[[ 0, 0 ],[ 2, 1 ]],[[ 0, 0 ],[ 1, 1 ]],[[ 1, 1 ],[ 2, 2 ]]],[[[ 0, 1 ],[ 0, 1 ]],[[ 0, 0 ],[ 1, 2 ]],[[ 0, 0 ],[ 1, 3 ]],[[ 0, 1 ],[ 2, 2 ]],[[ 0, 0 ],[ 0, 0 ]]],[[[ 1, 0 ],[ 2, 1 ]],[[ 1, 0 ],[ 2, 2 ]],[[ 0, 0 ],[ 1, 2 ]],[[ 0, 0 ],[ 3, 3 ]],[[ 1, 0 ],[ 2, 0 ]]],[[[ 0, 1 ],[ 0, 0 ]],[[ 1, 0 ],[ 2, 0 ]],[[ 1, 0 ],[ 2, 2 ]],[[ 0, 1 ],[ 0, 0 ]],[[ 0, 1 ],[ 2, 3 ]]],[[[ 0, 1 ],[ 0, 2 ]],[[ 0, 1 ],[ 2, 2 ]],[[ 1, 0 ],[ 0, 2 ]],[[ 1, 0 ],[ 2, 0 ]],[[ 0, 1 ],[ 0, 3 ]]],[[[ 1, 0 ],[ 1, 1 ]],[[ 1, 0 ],[ 0, 0 ]],[[ 0, 0 ],[ 1, 2 ]],[[ 0, 0 ],[ 2, 3 ]],[[ 1, 0 ],[ 0, 3 ]]],[[[ 0, 0 ],[ 1, 2 ]],[[ 0, 0 ],[ 0, 3 ]],[[ 0, 0 ],[ 2, 3 ]],[[ 0, 0 ],[ 1, 0 ]],[[ 1, 1 ],[ 0, 0 ]]],[[[ 0, 1 ],[ 3, 1 ]],[[ 0, 0 ],[ 3, 1 ]],[[ 1, 1 ],[ 0, 0 ]],[[ 1, 0 ],[ 2, 2 ]],[[ 0, 0 ],[ 0, 0 ]]],[[[ 1, 1 ],[ 1, 3 ]],[[ 0, 0 ],[ 1, 0 ]],[[ 1, 0 ],[ 2, 3 ]],[[ 0, 1 ],[ 2, 2 ]],[[ 0, 1 ],[ 1, 2 ]]],[[[ 0, 0 ],[ 3, 2 ]],[[ 0, 0 ],[ 2, 1 ]],[[ 1, 1 ],[ 1, 3 ]],[[ 1, 1 ],[ 0, 2 ]],[[ 1, 0 ],[ 1, 2 ]]],[[[ 1, 0 ],[ 3, 3 ]],[[ 0, 0 ],[ 0, 3 ]],[[ 0, 0 ],[ 1, 3 ]],[[ 1, 0 ],[ 0, 1 ]],[[ 1, 1 ],[ 2, 1 ]]],[[[ 0, 0 ],[ 0, 3 ]],[[ 0, 1 ],[ 1, 0 ]],[[ 0, 1 ],[ 3, 0 ]],[[ 0, 0 ],[ 2, 1 ]],[[ 1, 0 ],[ 3, 0 ]]],[[[ 0, 1 ],[ 2, 2 ]],[[ 1, 1 ],[ 3, 1 ]],[[ 1, 1 ],[ 3, 1 ]],[[ 0, 1 ],[ 0, 0 ]],[[ 0, 0 ],[ 2, 0 ]]],[[[ 1, 0 ],[ 0, 1 ]],[[ 1, 0 ],[ 2, 3 ]],[[ 1, 1 ],[ 3, 1 ]],[[ 1, 1 ],[ 1, 1 ]],[[ 0, 0 ],[ 1, 3 ]]],[[[ 1, 1 ],[ 0, 0 ]],[[ 0, 0 ],[ 2, 3 ]],[[ 0, 0 ],[ 1, 0 ]],[[ 1, 1 ],[ 3, 3 ]],[[ 1, 1 ],[ 1, 3 ]]],[[[ 0, 0 ],[ 0, 2 ]],[[ 0, 1 ],[ 1, 0 ]],[[ 1, 1 ],[ 1, 1 ]],[[ 1, 0 ],[ 2, 3 ]],[[ 0, 1 ],[ 0, 3 ]]],[[[ 1, 1 ],[ 2, 2 ]],[[ 0, 1 ],[ 1, 0 ]],[[ 0, 1 ],[ 1, 2 ]],[[ 1, 1 ],[ 2, 2 ]],[[ 0, 1 ],[ 3, 1 ]]],[[[ 0, 0 ],[ 1, 1 ]],[[ 0, 0 ],[ 2, 1 ]],[[ 0, 1 ],[ 2, 2 ]],[[ 0, 1 ],[ 3, 2 ]],[[ 0, 1 ],[ 0, 1 ]]],[[[ 1, 1 ],[ 3, 2 ]],[[ 1, 1 ],[ 2, 0 ]],[[ 0, 0 ],[ 3, 2 ]],[[ 0, 0 ],[ 2, 2 ]],[[ 0, 1 ],[ 3, 3 ]]],[[[ 0, 1 ],[ 1, 0 ]],[[ 0, 0 ],[ 1, 2 ]],[[ 0, 1 ],[ 3, 2 ]],[[ 0, 0 ],[ 3, 0 ]],[[ 1, 1 ],[ 2, 0 ]]],[[[ 0, 1 ],[ 2, 0 ]],[[ 0, 0 ],[ 1, 1 ]],[[ 0, 1 ],[ 3, 2 ]],[[ 0, 0 ],[ 2, 1 ]],[[ 1, 0 ],[ 0, 0 ]]],[[[ 1, 1 ],[ 3, 0 ]],[[ 1, 0 ],[ 2, 0 ]],[[ 0, 0 ],[ 0, 2 ]],[[ 0, 1 ],[ 1, 0 ]],[[ 1, 0 ],[ 1, 1 ]]],[[[ 1, 1 ],[ 1, 0 ]],[[ 0, 1 ],[ 1, 0 ]],[[ 1, 1 ],[ 2, 2 ]],[[ 0, 1 ],[ 2, 2 ]],[[ 1, 0 ],[ 3, 2 ]]],[[[ 1, 1 ],[ 1, 1 ]],[[ 0, 0 ],[ 3, 1 ]],[[ 0, 1 ],[ 0, 0 ]],[[ 1, 0 ],[ 2, 2 ]],[[ 0, 0 ],[ 3, 2 ]]],[[[ 1, 1 ],[ 3, 1 ]],[[ 0, 0 ],[ 0, 2 ]],[[ 1, 0 ],[ 2, 3 ]],[[ 0, 1 ],[ 3, 2 ]],[[ 1, 1 ],[ 0, 2 ]]],[[[ 1, 0 ],[ 2, 0 ]],[[ 0, 0 ],[ 0, 3 ]],[[ 0, 0 ],[ 2, 3 ]],[[ 1, 0 ],[ 2, 2 ]],[[ 1, 1 ],[ 3, 0 ]]],[[[ 1, 0 ],[ 0, 2 ]],[[ 0, 0 ],[ 0, 2 ]],[[ 0, 1 ],[ 2, 2 ]],[[ 1, 1 ],[ 2, 2 ]],[[ 0, 0 ],[ 0, 2 ]]],[[[ 1, 0 ],[ 3, 0 ]],[[ 1, 1 ],[ 0, 2 ]],[[ 1, 1 ],[ 3, 3 ]],[[ 1, 0 ],[ 2, 3 ]],[[ 1, 1 ],[ 0, 2 ]]],[[[ 1, 1 ],[ 2, 3 ]],[[ 1, 0 ],[ 0, 0 ]],[[ 0, 0 ],[ 1, 3 ]],[[ 0, 1 ],[ 3, 0 ]],[[ 0, 1 ],[ 3, 3 ]]],[[[ 0, 0 ],[ 0, 1 ]],[[ 0, 0 ],[ 2, 1 ]],[[ 0, 0 ],[ 3, 1 ]],[[ 0, 0 ],[ 3, 1 ]],[[ 0, 1 ],[ 0, 2 ]]],[[[ 1, 0 ],[ 3, 1 ]],[[ 0, 0 ],[ 2, 3 ]],[[ 0, 0 ],[ 1, 1 ]],[[ 1, 0 ],[ 2, 3 ]],[[ 0, 1 ],[ 0, 2 ]]],[[[ 0, 0 ],[ 2, 0 ]],[[ 0, 1 ],[ 3, 2 ]],[[ 0, 1 ],[ 0, 2 ]],[[ 0, 0 ],[ 1, 2 ]],[[ 0, 0 ],[ 3, 1 ]]],[[[ 1, 1 ],[ 2, 1 ]],[[ 0, 0 ],[ 3, 3 ]],[[ 0, 0 ],[ 3, 2 ]],[[ 1, 1 ],[ 2, 0 ]],[[ 1, 0 ],[ 3, 1 ]]],[[[ 1, 0 ],[ 0, 0 ]],[[ 0, 0 ],[ 1, 0 ]],[[ 0, 1 ],[ 3, 0 ]],[[ 1, 1 ],[ 0, 0 ]],[[ 0, 0 ],[ 2, 0 ]]],[[[ 0, 0 ],[ 2, 3 ]],[[ 0, 1 ],[ 2, 2 ]],[[ 0, 0 ],[ 0, 3 ]],[[ 0, 1 ],[ 0, 2 ]],[[ 1, 1 ],[ 2, 3 ]]],[[[ 1, 0 ],[ 1, 2 ]],[[ 0, 0 ],[ 2, 3 ]],[[ 0, 1 ],[ 0, 0 ]],[[ 1, 1 ],[ 1, 3 ]],[[ 1, 1 ],[ 0, 0 ]]],[[[ 0, 1 ],[ 3, 3 ]],[[ 1, 0 ],[ 2, 1 ]],[[ 1, 0 ],[ 0, 0 ]],[[ 0, 1 ],[ 1, 0 ]],[[ 1, 0 ],[ 1, 2 ]]],[[[ 1, 0 ],[ 2, 2 ]],[[ 0, 1 ],[ 3, 0 ]],[[ 1, 1 ],[ 0, 2 ]],[[ 0, 0 ],[ 3, 0 ]],[[ 0, 1 ],[ 2, 0 ]]],[[[ 0, 1 ],[ 1, 2 ]],[[ 0, 1 ],[ 3, 2 ]],[[ 0, 0 ],[ 3, 3 ]],[[ 0, 0 ],[ 1, 3 ]],[[ 0, 1 ],[ 0, 3 ]]],[[[ 1, 0 ],[ 0, 3 ]],[[ 0, 0 ],[ 0, 1 ]],[[ 0, 0 ],[ 2, 1 ]],[[ 1, 0 ],[ 0, 1 ]],[[ 1, 1 ],[ 1, 1 ]]],[[[ 1, 1 ],[ 3, 3 ]],[[ 0, 0 ],[ 3, 0 ]],[[ 1, 1 ],[ 2, 0 ]],[[ 0, 0 ],[ 2, 3 ]],[[ 1, 1 ],[ 1, 1 ]]],[[[ 1, 1 ],[ 0, 1 ]],[[ 0, 0 ],[ 2, 3 ]],[[ 0, 0 ],[ 2, 0 ]],[[ 1, 1 ],[ 0, 2 ]],[[ 0, 0 ],[ 2, 1 ]]],[[[ 1, 1 ],[ 0, 2 ]],[[ 1, 1 ],[ 2, 0 ]],[[ 0, 1 ],[ 0, 2 ]],[[ 0, 1 ],[ 0, 0 ]],[[ 1, 1 ],[ 1, 0 ]]],[[[ 0, 0 ],[ 0, 0 ]],[[ 0, 0 ],[ 1, 2 ]],[[ 0, 1 ],[ 1, 2 ]],[[ 0, 1 ],[ 2, 2 ]],[[ 1, 0 ],[ 2, 1 ]]],[[[ 0, 1 ],[ 2, 1 ]],[[ 0, 1 ],[ 3, 0 ]],[[ 1, 1 ],[ 3, 3 ]],[[ 1, 1 ],[ 2, 0 ]],[[ 0, 1 ],[ 3, 0 ]]],[[[ 0, 1 ],[ 3, 0 ]],[[ 0, 0 ],[ 2, 3 ]],[[ 0, 0 ],[ 3, 1 ]],[[ 0, 1 ],[ 2, 0 ]],[[ 1, 1 ],[ 3, 0 ]]],[[[ 0, 0 ],[ 1, 3 ]],[[ 0, 0 ],[ 1, 2 ]],[[ 1, 0 ],[ 2, 1 ]],[[ 1, 0 ],[ 2, 0 ]],[[ 1, 1 ],[ 3, 3 ]]],[[[ 0, 0 ],[ 2, 2 ]],[[ 0, 1 ],[ 1, 2 ]],[[ 0, 0 ],[ 0, 2 ]],[[ 0, 1 ],[ 3, 0 ]],[[ 1, 0 ],[ 3, 3 ]]],[[[ 0, 1 ],[ 0, 3 ]],[[ 1, 1 ],[ 2, 2 ]],[[ 0, 1 ],[ 3, 0 ]],[[ 1, 1 ],[ 1, 1 ]],[[ 1, 0 ],[ 3, 3 ]]],[[[ 0, 1 ],[ 2, 3 ]],[[ 1, 0 ],[ 2, 2 ]],[[ 0, 0 ],[ 3, 0 ]],[[ 1, 1 ],[ 3, 3 ]],[[ 1, 1 ],[ 3, 0 ]]],[[[ 0, 0 ],[ 3, 0 ]],[[ 1, 1 ],[ 0, 0 ]],[[ 0, 0 ],[ 0, 1 ]],[[ 1, 1 ],[ 3, 3 ]],[[ 0, 1 ],[ 3, 0 ]]],[[[ 1, 1 ],[ 2, 0 ]],[[ 1, 1 ],[ 2, 2 ]],[[ 0, 0 ],[ 3, 3 ]],[[ 0, 0 ],[ 1, 1 ]],[[ 1, 1 ],[ 0, 1 ]]],[[[ 0, 0 ],[ 3, 1 ]],[[ 0, 0 ],[ 3, 3 ]],[[ 0, 0 ],[ 3, 1 ]],[[ 0, 0 ],[ 3, 1 ]],[[ 0, 0 ],[ 0, 3 ]]],[[[ 0, 0 ],[ 2, 1 ]],[[ 0, 0 ],[ 0, 3 ]],[[ 1, 1 ],[ 2, 0 ]],[[ 1, 1 ],[ 2, 0 ]],[[ 1, 1 ],[ 3, 2 ]]],[[[ 1, 0 ],[ 1, 0 ]],[[ 0, 0 ],[ 2, 1 ]],[[ 0, 0 ],[ 3, 0 ]],[[ 1, 0 ],[ 2, 1 ]],[[ 1, 1 ],[ 0, 1 ]]],[[[ 0, 1 ],[ 1, 3 ]],[[ 1, 0 ],[ 2, 0 ]],[[ 1, 1 ],[ 2, 0 ]],[[ 0, 0 ],[ 3, 1 ]],[[ 1, 0 ],[ 2, 0 ]]],[[[ 1, 0 ],[ 2, 3 ]],[[ 1, 1 ],[ 0, 2 ]],[[ 0, 0 ],[ 0, 3 ]],[[ 0, 1 ],[ 2, 2 ]],[[ 1, 0 ],[ 2, 3 ]]],[[[ 1, 1 ],[ 1, 2 ]],[[ 0, 0 ],[ 0, 0 ]],[[ 0, 0 ],[ 3, 2 ]],[[ 1, 1 ],[ 0, 0 ]],[[ 1, 1 ],[ 0, 0 ]]]};




Ass_better_RP_zetas:=AssociativeArray();
for zeta1 in set_zeta do
  for zetas in set_better_RP_zetas do
    if zeta1 eq zetas[1] then 
      Ass_better_RP_zetas[zeta1]:=zetas;
    end if;
  end for;
end for;
assert(Keys(Ass_better_RP_zetas) eq set_zeta);







/*
sub_RP_zeta_Ass:=AssociativeArray();
for zeta1 in set_zeta do
  sub_RP_zeta_Ass[zeta1]:={};
  for zetas in sub_RP_zeta do
    if zetas[1] eq zeta1 then
      sub_RP_zeta_Ass[zeta1]:=sub_RP_zeta_Ass[zeta1] join {zetas};
    end if;
  end for;
end for;
*/





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





//mumfordから計算した方.
//こっちがあってる.
precomp_for_add:=AssociativeArray(); 
for zeta1 in set_zeta do
  zetas:=Ass_better_RP_zetas[zeta1];
  for etaa in set_zeta do
    assert (zeta1 eq zetas[1]);
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
  
    precomp_for_add[[zeta1,etaa]]
    :=<ind_zeta1,ind_zeta2,ind_zeta3,ind_zeta4,coff>;
  end for;
end for;





//the following set depends on the choice of "set_better_RP_zetas".
positive_zeta:=
{[[ 1, 1 ],[ 1, 1 ]],[[ 0, 0 ],[ 3, 2 ]],[[ 1, 1 ],[ 1, 3 ]],[[ 0, 0 ],[ 3, 3 ]],[[ 0, 0 ],[ 3, 0 ]],[[ 0, 0 ],[ 3, 1 ]],[[ 0, 1 ],[ 2, 2 ]],[[ 0, 1 ],[ 2, 0 ]],[[ 0, 0 ],[ 2, 2 ]],[[ 0, 0 ],[ 2, 3 ]],[[ 0, 0 ],[ 2, 0 ]],[[ 0, 0 ],[ 2, 1 ]],[[ 1, 1 ],[ 2, 2 ]],[[ 1, 1 ],[ 2, 0 ]],[[ 1, 0 ],[ 0, 0 ]],[[ 1, 1 ],[ 3, 3 ]],[[ 1, 0 ],[ 0, 1 ]],[[ 1, 0 ],[ 0, 2 ]],[[ 1, 1 ],[ 3, 1 ]],[[ 0, 0 ],[ 1, 0 ]],[[ 1, 0 ],[ 0, 3 ]],[[ 1, 0 ],[ 2, 2 ]],[[ 0, 0 ],[ 1, 1 ]],[[ 0, 0 ],[ 1, 2 ]],[[ 1, 0 ],[ 2, 3 ]],[[ 0, 0 ],[ 1, 3 ]],[[ 1, 0 ],[ 2, 0 ]],[[ 1, 0 ],[ 2, 1 ]],[[ 0, 1 ],[ 0, 0 ]],[[ 1, 1 ],[ 0, 0 ]],[[ 0, 1 ],[ 0, 2 ]],[[ 0, 1 ],[ 1, 0 ]],[[ 1, 1 ],[ 0, 2 ]],[[ 0, 1 ],[ 1, 2 ]],[[ 0, 0 ],[ 0, 0 ]],[[ 0, 0 ],[ 0, 1 ]],[[ 0, 0 ],[ 0, 2 ]],[[ 0, 0 ],[ 0, 3 ]],[[ 0, 1 ],[ 3, 2 ]],[[ 0, 1 ],[ 3, 0 ]]};


pm_for_zeta1:=AssociativeArray();
for zeta1 in set_zeta do
  if zeta1 in positive_zeta then
    pm_for_zeta1[zeta1]:=1;
  else
    pm_for_zeta1[zeta1]:=-1;
  end if;
end for;
assert (Keys(pm_for_zeta1)eq set_zeta);





//_______________________________
//冪集合を作る関数.

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
//etaを作る. @1

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



//上のetaの逆写像を作る. 2点以下の集合で返す. 
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
 





//---------------------------------------------




//lv22の指標を拡張する. 
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


//2つのAssociative arrayが同じか判定.

function eq_Assoc(A,B)
  assert (Category(A) eq Assoc);
  assert (Category(B) eq Assoc);

  if Keys(A) ne Keys(B) then
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







//==============
//multiply projective factor s.t. [0,0]=1 or [0,0,0,0]=1.

function profac(tc)

  if Keys(tc) eq lv22keys then
    const:=tc[[0,0,0,0]];
    for key in lv22keys do
      tc[key]:=tc[key]/const;
    end for;
    return tc;
  end if;

  if Keys(tc) eq lv4keys then 
    const:=tc[[0,0]];
    for key in lv4keys do
      tc[key]:=tc[key]/const;
    end for;
    return tc;
  end if;
end function;










//End of global_setting.
//=======================================================

