//===================================================
//Start of isogeny.m

//As usual, we assume dim g=2, level n=4.
//degree l is odd prime.


//decision if K is istropic subgroup w.r.t. Weil paring for l.
function Is_isotropic(sub_K,J,l,iso_map)
  g:=Dimension(J);
  group_K:=sub_K`subgroup;  //`
  gen_K:=Generators(group_K);
  assert (#gen_K eq g);
  return forall{ptpt:ptpt in CartesianPower(gen_K,2)| WeilPairing(iso_map(ptpt[1]),iso_map(ptpt[2]),l) eq 1};
end function;


//construct informatino of torision point J[l].
function torsion_pt(J,l)
  ts_pt:=AssociativeArray();  //wanted.
  g:=Dimension(J);
  the_order:=l^(2*g);  

  for deg in {1..12} do
    ex_J:=BaseChange(J,deg);
    order_ex_J:=#ex_J;
    if (order_ex_J mod the_order) eq 0 then
      ex_deg:=deg;
      ex_J:=BaseChange(J,ex_deg);
      Abl_J,iso_map:=AbelianGroup(ex_J); //take a lot time.
      J_l:={g:g in Sylow(Abl_J,l)|l*g eq Sylow(Abl_J,l)!0}; //l-torsion pt of J.
      if #J_l eq l^(2*g) then
        Abl_J_l:=sub<Abl_J|J_l>;
        assert (#Generators(Abl_J_l) eq 2*g);
        Gen_J_l:={iso_map(gen):gen in Generators(Abl_J_l)};
        
        Cand_K:=<sub_K : sub_K in  Subgroups(Abl_J_l)|sub_K`order eq l^g>; //`
        Istr:=<Cand_K[index] : index in {1..#Cand_K} | Is_isotropic(Cand_K[index],J,l,iso_map)>;
        regular_degree:=&*[(l^k+1) :k in {1..g}];
        assert (#Istr eq regular_degree);

        ts_pt["J"]:=ex_J;
        ts_pt["group_J"]:=AbelianGroup(ex_J);
        ts_pt["field"]:=BaseField(ex_J);
        ts_pt["basis"]:=Gen_J_l; //one of basis.
        ts_pt["order"]:=l;
        ts_pt["card"]:=l^(2*g);  //#J[l].
        ts_pt["group"]:=Abl_J_l; //abstract group.
        ts_pt["point"]:={iso_map(pt):pt in Abl_J_l}; //subset of J.
        ts_pt["Grp_to_J"]:=iso_map; //map (Z/lZ)^(2g) -> J[l].
        ts_pt["reg_deg"]:=regular_degree;
        ts_pt["isotropic"]:=Istr;

        return ts_pt;   
        break deg;
      end if;
    end if;
  end for;
  return "the base field of J[l] is too big.";
end function;






//return basis of K as point of J.
function tspt_to_basis(ts_pt,index) 
  Istr:=ts_pt["isotropic"];
  sub_K:=Istr[index]`subgroup; //`
  iso_map:=ts_pt["Grp_to_J"];
  return {iso_map(gen):gen in Generators(sub_K)};
end function;






/*
//get one isotropic subgrp K s.t. the base field is not big.
function take_isotropic(J,l)
  istr_K:=AssociativeArray();  //wanted.
  g:=Dimension(J);

  for deg in {1..8} do
    ex_J:=BaseChange(J,deg);
    order_ex_J:=#ex_J;
    if (order_ex_J mod l^g) eq 0 then
      Abl_J,iso_map:=AbelianGroup(ex_J); //take a lot time.
      J_l:={g:g in Sylow(Abl_J,l)|l*g eq Sylow(Abl_J,l)!0}; //l-torsion pt of J.
      Abl_J_l:=sub<Abl_J|J_l>;
      for rec_K in Subgroups(Abl_J_l) do
        if rec_K`order eq l^g then  //`
          if Is_isotropic(rec_K,J,l,iso_map) then
            grp_K:=rec_K`subgroup; //`
            istr_K["J"]:=ex_J;
            istr_K["basis"]:={iso_map(gen):gen in Generators(grp_K)};
            istr_K["seq_basis"]:=[iso_map(gen):gen in Generators(grp_K)];
            istr_K["group"]:=grp_K;   
            istr_K["field"]:=BaseField(ex_J);
            istr_K["K"]:={iso_map(elm): elm in grp_K};
            return istr_K;
          end if;
        end if;
      end for;
    end if;
  end for;
  return "the base field of J[l] is too big.";
end function;
*/



//get one isotropic subgrp K s.t. the base field is not big.
function take_one_isotropic(J,l,lim)
  istr_K:=AssociativeArray();  //wanted.
  g:=Dimension(J);

  for deg in {1..lim} do  //search lim-deg extension.
    ex_J:=BaseChange(J,deg);
    order_ex_J:=#ex_J;
    if (order_ex_J mod l^g) eq 0 then
      Abl_J,iso_map:=AbelianGroup(ex_J); //take a lot time.
      J_l:={g:g in Sylow(Abl_J,l)|l*g eq Sylow(Abl_J,l)!0}; //l-torsion pt of J.
      Abl_J_l:=sub<Abl_J|J_l>;
      for rec_K in Subgroups(Abl_J_l) do
        if rec_K`order eq l^g then  //`
          if Is_isotropic(rec_K,J,l,iso_map) then

            "found over the following base field.";
            BaseField(ex_J);

            grp_K:=rec_K`subgroup; //`
            istr_K["J"]:=ex_J;
            istr_K["basis"]:={iso_map(gen):gen in Generators(grp_K)};
            istr_K["seq_basis"]:=[iso_map(gen):gen in Generators(grp_K)];
            istr_K["group"]:=grp_K;   
            istr_K["field"]:=BaseField(ex_J);
            istr_K["K"]:={iso_map(elm): elm in grp_K};
            return istr_K;
          end if;
        end if;
      end for;
    end if;
  end for;
  "nothing over given degree extension.";
  return false;
end function;






//get one isotropic subgrp K s.t. the base field is not big.
function take_one_isotropic_2(J,l,lim)
  istr_K:=AssociativeArray();  //wanted.
  g:=Dimension(J);

  for deg in {1..lim} do  //search lim-deg extension.
    deg;
    ex_J:=BaseChange(J,deg);
    "pt7";
    order_ex_J:=#ex_J;
    "pt8";
    (order_ex_J mod l^g);
    "pt9";
    if (order_ex_J mod l^g) eq 0 then
      "pt1";
      Abl_J,iso_map:=AbelianGroup(ex_J); //take a lot time.
      "pt2";
      J_l:={g:g in Sylow(Abl_J,l)|l*g eq Sylow(Abl_J,l)!0}; //l-torsion pt of J.
      "pt3";
      Abl_J_l:=sub<Abl_J|J_l>;
      "pt4";
      for rec_K in Subgroups(Abl_J_l) do
        ".";
        if rec_K`order eq l^g then  //`
          "pt5";
          if Is_isotropic(rec_K,J,l,iso_map) then
            "pt6";

            "found over the following base field.";
            BaseField(ex_J);

            grp_K:=rec_K`subgroup; //`
            istr_K["J"]:=ex_J;
            istr_K["basis"]:={iso_map(gen):gen in Generators(grp_K)};
            istr_K["seq_basis"]:=[iso_map(gen):gen in Generators(grp_K)];
            istr_K["group"]:=grp_K;   
            istr_K["field"]:=BaseField(ex_J);
            istr_K["K"]:={iso_map(elm): elm in grp_K};
            return istr_K;
          end if;
        end if;
      end for;
    end if;
  end for;
  "nothing over given degree extension.";
  return false;
end function;




//---------------------------------------------------------
//precomputation "index_t" and "index_j" for l.


//Lagrange's four square theorem.
function sum_of_4sq(l)
  flsq:=Floor(Sqrt(l));
  for a1 in [0..flsq] do
    for a2 in [a1..flsq] do
      for a3 in [a2..flsq] do
        for a4 in [a3..flsq] do
          if a1^2+a2^2+a3^2+a4^2 eq l then
            return [a4,a3,a2,a1];
          end if;
        end for;
      end for;
    end for;
  end for;
end function;




function const_Mat_F(l)
  assert (IsPrime(l));
  assert (l ne 2);

  if (((l-3) mod 4) eq 0) then  //l=3 mod4.
    sum4sq:=sum_of_4sq(l);
    a1:=sum4sq[1];
    a2:=sum4sq[2];
    a3:=sum4sq[3];
    a4:=sum4sq[4];
    //l=a1^2+a2^2+a3^2+a4^2.

    Mat_F:=Matrix(IntegerRing(),4,4,[a1,-a2,-a3,-a4, a2,a1,a4,-a3, a3,-a4,a1,a2, a4,a3,-a2,a1]);
    r:=4;
  end if;

  if ((l-1) mod 4) eq 0 then  //l=1 mod4.
    r:=2;
    for i in [1..(l-1)] do
      if IsSquare(l-i^2) then
        _,j:=IsSquare(l-i^2);
        Mat_F:=Matrix(IntegerRing(),2,2,[i,-j, j,i]);
        break i;
      end if;
    end for;
  end if;

  assert (Transpose(Mat_F)*Mat_F eq ScalarMatrix(IntegerRing(), r, l));
  return Mat_F;
end function;





function const_index_t_j(l,Mat_F)
  r:=NumberOfRows(Mat_F);
  index_t:={};  //wanted.
  vector_t:={[i_1,i_2]:i_1,i_2 in {0..(l-1)}};
  for all_t in CartesianPower(vector_t,r) do
    count:=0;
    for j in {1..r} do //for the s_th column.
      if ((&+[all_t[i][1]*Mat_F[i][j]: i in {1..r}]) mod l) eq 0 then
        if ((&+[all_t[i][2]*Mat_F[i][j]: i in {1..r}]) mod l) eq 0 then
        count:=count+1;
        end if;
      end if;
    end for;
    if count eq r then
      index_t:=index_t join {all_t};
    end if;
  end for;

  //inv_F is inverse matrix of Mat_F over Z/nZ. (n=4).
  inv_F:=l*Transpose(Mat_F);
  index_j:=AssociativeArray();
  for key in lv4keys do
    index_j[key]:=[];
    for j in {1..r} do
      index_j[key][j]:=[(key[1]*inv_F[1][j])mod 4,(key[2]*inv_F[1][j])mod 4];
    end for;
  end for;

  return r,index_t,index_j;
end function;




function const_index_t_j_2(l,Mat_F)
  r:=NumberOfRows(Mat_F);
  ZlZ:=quo<IntegerRing()|l>;
  Mat_Fl:=ChangeRing(Mat_F,ZlZ);
  vec_tl:=Nullspace(Mat_Fl);
  set_vec_tl:={x:x in vec_tl};
  set_vec_t:={};
  "CT1";
  for x in set_vec_tl do
    int_x:=[];
    for i in {1..r} do
      int_x[i]:=IntegerRing()!(x[i]);
    end for;
    set_vec_t join:={int_x};
  end for;
  "CT2";
  assert(#set_vec_tl eq #set_vec_t);
  "CT3";
  index_t:={};
  for tt in CartesianPower(set_vec_t,2) do
    tt;
    vec_t:=<[tt[1][i],tt[2][i]]:i in [1..r]>;
    /*
    for i in [1..r] do
      vec_t[i]:=[tt[1][i],tt[2][i]];
    end for;
    */
    index_t join:={vec_t};
  end for;
  "CT4";
  assert(#index_t eq #set_vec_t^2);
  "CT5";

   //inv_F is inverse matrix of Mat_F over Z/nZ. (n=4).
  inv_F:=l*Transpose(Mat_F);
  index_j:=AssociativeArray();
  "CT6";
  for key in lv4keys do
    index_j[key]:=[];
    for j in {1..r} do
      index_j[key][j]:=[(key[1]*inv_F[1][j])mod 4,(key[2]*inv_F[1][j])mod 4];
    end for;
  end for;
  "CT7";

  return r,index_t,index_j;
end function;





function const_index_t_j_3(l,Mat_F)
  r:=NumberOfRows(Mat_F);
  ZlZ:=quo<IntegerRing()|l>;
  Mat_Fl:=ChangeRing(Mat_F,ZlZ);
  vec_tl:=Nullspace(Mat_Fl);
  set_vec_tl:={x:x in vec_tl};
  set_vec_t:={};
  for x in set_vec_tl do
    int_x:=[];
    for i in {1..r} do
      int_x[i]:=IntegerRing()!(x[i]);
    end for;
    set_vec_t join:={int_x};
  end for;
  assert(#set_vec_tl eq #set_vec_t);
  index_t:={};
  if r eq 2 then
    index_t:={<[tt[1][1],tt[2][1]],[tt[1][2],tt[2][2]]>:tt in CartesianPower(set_vec_t,2)};
  end if;

  "it takes time.";
  if r eq 4 then
    index_t:={<[tt1[1],tt2[1]],[tt1[2],tt2[2]],[tt1[3],tt2[3]],[tt1[4],tt2[4]]>:tt1,tt2 in set_vec_t};
  end if;
  "fin.";

  assert(#index_t eq #set_vec_t^2);

   //inv_F is inverse matrix of Mat_F over Z/nZ. (n=4).
  inv_F:=l*Transpose(Mat_F);
  index_j:=AssociativeArray();
  "CT6";
  for key in lv4keys do
    index_j[key]:=[];
    for j in {1..r} do
      index_j[key][j]:=[(key[1]*inv_F[1][j])mod 4,(key[2]*inv_F[1][j])mod 4];
    end for;
  end for;

  return r,index_t,index_j;
end function;



//--------------------------------------------------





function const_inv_lv4tc(lv4tc)
  m_lv4tc:=AssociativeArray();
  for index_1 in {0..3} do
    for index_2 in {0..3} do
      m_lv4tc[[index_1,index_2]]:=lv4tc[[(4-index_1)mod 4,(4-index_2)mod 4]];
    end for;
  end for;
  return m_lv4tc;
end function;


//first, we compute theta null point of the codomain from kernel basis.

//K=(Z/lZ)^g. tc_e1,tc_e2 are the given basis.
//tc_e1pe2 is theta cordinate of e_1+e_2.

function modify_basis(lv4tnp,l,lv4tc1,lv4tc2,lv4tc1p2)
  inv_lv4tc1:=const_inv_lv4tc(lv4tc1);
  inv_lv4tc2:=const_inv_lv4tc(lv4tc2);
  inv_lv4tc1p2:=const_inv_lv4tc(lv4tc1p2);

  l_d:=IntegerRing()!((l+1)/2)-1;  //l'=(l+1)/2.
  lm_j_lpow:=[];

  for i_0 in lv4keys do
    if (mult(lv4tnp,l_d+1,lv4tc1)[i_0] ne 0) then
      lm_j_lpow[1]:=mult(lv4tnp,l_d,inv_lv4tc1)[i_0]/mult(lv4tnp,l_d+1,lv4tc1)[i_0];
      break i_0;
    end if;
  end for;

  for i_0 in lv4keys do
    if (mult(lv4tnp,l_d+1,lv4tc2)[i_0] ne 0) then
      lm_j_lpow[2]:=mult(lv4tnp,l_d,inv_lv4tc2)[i_0]/mult(lv4tnp,l_d+1,lv4tc2)[i_0];
      break i_0;
    end if;
  end for;

  for i_0 in lv4keys do
    if (mult(lv4tnp,l_d+1,lv4tc1p2)[i_0] ne 0) then
      lm_j_lpow[3]:=mult(lv4tnp,l_d,inv_lv4tc1p2)[i_0]/mult(lv4tnp,l_d+1,lv4tc1p2)[i_0];
      break i_0;
    end if;
  end for;

  Fil:=Parent(lm_j_lpow[1]);
  Fil<y>:=PolynomialRing(Fil);
  lm_j1:=RootsInSplittingField(y^l-(lm_j_lpow[1]))[1][1];

  Fil:=Parent(lm_j_lpow[2]);
  Fil<y>:=PolynomialRing(Fil);
  lm_j2:=RootsInSplittingField(y^l-(lm_j_lpow[2]))[1][1];

  Fil:=Parent(lm_j_lpow[3]);
  Fil<y>:=PolynomialRing(Fil);
  lm_j12:=RootsInSplittingField(y^l-(lm_j_lpow[3]))[1][1];

  for key in lv4keys do
    lv4tc1[key]*:=lm_j1;
    lv4tc2[key]*:=lm_j2;
    lv4tc1p2[key]*:=lm_j12;
  end for;

  return lv4tc1,lv4tc2,lv4tc1p2;
end function;









function lv4tnp_of_codomain(l,r,index_t,index_j,lv4tnp,tc_e1,tc_e2,tc_e1pe2)
  tnp_codomain:=AssociativeArray();  //lv4tnp of codomain.
 
  _,base_field:=global_field_of_seq([tc_e1,tc_e2,tc_e1pe2]);
  tc_e1,tc_e2,tc_e1pe2:=modify_basis(lv4tnp,l,tc_e1,tc_e2,tc_e1pe2);

  lin_com:=linear_combination(lv4tnp,l,tc_e1,tc_e2,tc_e1pe2);

  for key in lv4keys do
    tnp_codomain[key]:=&+[&*[lin_com[t[j]][index_j[key][j]]:j in {1..r}]:t in index_t];
    tnp_codomain[key]:=(base_field)!(tnp_codomain[key]);
  end for;
  return tnp_codomain;
end function;


//-----------------------------------------
//image of point.



function compute_mu_new(lv4tnp,tc_e1,tc_e2,l,tc_x,tc_xpe1,tc_xpe2)
  key:=[0,0];
  mu_1_lpow:=tc_x[key]/(ThreePtLadder_plus(lv4tnp,l,tc_e1,tc_x,tc_xpe1)[key]);
  mu_2_lpow:=tc_x[key]/(ThreePtLadder_plus(lv4tnp,l,tc_e2,tc_x,tc_xpe2)[key]);

  Fil:=Parent(mu_1_lpow);
  Fil<y>:=PolynomialRing(Fil);
  mu_j1:=RootsInSplittingField(y^l-mu_1_lpow)[1][1];
  Fil:=Parent(mu_2_lpow);
  Fil<y>:=PolynomialRing(Fil);
  mu_j2:=RootsInSplittingField(y^l-mu_2_lpow)[1][1];
  return mu_j1,mu_j2;
end function;






function image_of_point(lincom_e1e2,l,Mat_F,index_t,index_j,lv4tnp,tc_e1,tc_e2,tc_e1pe2,tc_x,tc_xpe1,tc_xpe2)
  r:=NumberOfRows(Mat_F);
  max_coff_x:=Max({Mat_F[j][1]: j in {1..r}});
  img_lv4tc:=AssociativeArray();
  mu_j1,mu_j2:=compute_mu_new(lv4tnp,tc_e1,tc_e2,l,tc_x,tc_xpe1,tc_xpe2);
  for key in lv4keys do
    tc_xpe1[key] *:=mu_j1;
    tc_xpe2[key] *:=mu_j2;
  end for;

  time_lincom_ip:=Time();
  //construct linear combination of x,e_1,e_2.
  lin_com:=lincom_xe1e2(lincom_e1e2,lv4tnp,l,max_coff_x,tc_e1,tc_e2,tc_e1pe2,tc_x,tc_xpe1,tc_xpe2);
  //"Lin_com time for each pt.",Time(time_lincom_ip);

  Xpt:=AssociativeArray();
  for t in index_t do  //t=(t_1,..,t_r).
    Xpt[t]:=[];
    for j in {1..r} do
      Xpt[t][j]:=lin_com[[Mat_F[j][1],t[j][1],t[j][2]]]; //theta cordinate of X_j+t_j.
    end for;
  end for;
  for key in lv4keys do
    img_lv4tc[key]:=&+[&*[Xpt[t][j][index_j[key][j]]:j in {1..r}]:t in index_t];
  end for;
  return img_lv4tc;
end function;




//End of isogeny.m
//===================================================
