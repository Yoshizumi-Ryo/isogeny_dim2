//==============================================
//Start of Mum_to_theta7


//We can apply this function any Ros form not only 0,1.
function Ros_to_lv22tnp(Ros)
  lv22tnpsq:=AssociativeArray(); 
  lv22tnpsq[N[0]]:=1; 

  //first we use Thomae for getting 4th power.
  lv22tnp4p:=AssociativeArray();
  U:={1,3,5};

  for T in {{2,3,4,5},{4,5},{1,2},{3,4}} do
  
    XX:=((-1)^(#(T meet U)))*(&*[(Ros[i]-Ros[j]): i in ({} sdiff U), j in ({1..5} diff ({} sdiff U))])/(&*[(Ros[i]-Ros[j]): i in (T sdiff U), j in ({1..5} diff (T sdiff U))]);
    
    sq:=RootsInSplittingField(x^2-XX);
    lv22tnpsq[eta[T]]:=sq[1][1];
  end for;

  //Then, we caluculate others by[87](20).
  //U:={1,3,5};
  function TE(V,S) 
    return lv22tnpsq[eta[U sdiff V sdiff S]];
  end function;

  difa:=AssociativeArray();   //prepare <a_i-a_j>.
  for i in {1..5} do
    for j in {1..5} do
      if i le j then 
        difa[[i,j]]:=Ros[j]-Ros[i];
      end if;
      if i gt j then
        difa[[i,j]]:=Ros[i]-Ros[j];
      end if;
    end for;
  end for;

  //[1,0,0,1].
  i:=2;
  j:=5;
  k:=1;
  V:={2,5,3};
  lv22tnpsq[eta[U sdiff V sdiff {j,k}]]:=(difa[[k,i]]/difa[[k,j]])*TE(V,{j,0})*TE(V,{i,k})/TE(V,{i,0});

  //[1,1,0,0].
  i:=2;
  j:=3;
  k:=1;
  V:={2,3,4};
  lv22tnpsq[eta[U sdiff V sdiff {i,0}]]:=(difa[[k,i]]/difa[[k,j]])*TE(V,{j,0})*TE(V,{i,k})/TE(V,{j,k});

  //[0,0,1,1].
  i:=5;
  j:=1;
  k:=2;
  V:={1,4,5};
  //lv22tnpsq[eta[U sdiff V sdiff {j,k}]]:=(difa[[k,i]]/difa[[k,j]])*TE(V,{j,0})*TE(V,{i,k})/TE(V,{i,0});
  lv22tnpsq[eta[U sdiff V sdiff {j,k}]]:=(difa[[k,i]]/difa[[k,j]])*lv22tnpsq[[1,0,0,1]]*TE(V,{i,k})/TE(V,{i,0});

  //[0,1,1,0].
  V:={3,1,5};
  i:=3;
  j:=1;
  k:=2;
  //lv22tnpsq[eta[U sdiff V sdiff {i,0}]]:=(difa[[k,i]]/difa[[k,j]])*TE(V,{j,0})*TE(V,{i,k})/TE(V,{j,k});
  lv22tnpsq[eta[U sdiff V sdiff {i,0}]]:=(difa[[k,i]]/difa[[k,j]])*TE(V,{j,0})*lv22tnpsq[[1,1,0,0]]/TE(V,{j,k});

  //[1,1,1,1]
  V:={1,2,3};
  i:=2;
  j:=3;
  k:=4;
  //lv22tnpsq[eta[U sdiff V sdiff {j,0}]]:=(difa[[k,j]]/difa[[k,i]])*TE(V,{i,0})*TE(V,{j,k})/TE(V,{i,k});
  lv22tnpsq[eta[U sdiff V sdiff {j,0}]]:=(difa[[k,j]]/difa[[k,i]])*lv22tnpsq[[0,0,1,1]]*TE(V,{j,k})/TE(V,{i,k});

  lv22tnp:=AssociativeArray();
  for index in {1..10} do
    if lv22tnpsq[F[index]] in IntegerRing() then
      Fld:=K;
    else 
      Fld:=Parent(lv22tnpsq[F[index]]);
    end if;
    Fldx<y>:=PolynomialRing(Fld);
    roots:=RootsInSplittingField(y^2-lv22tnpsq[F[index]]);
    lv22tnp[F[index]]:=roots[1][1];
  end for;

  for index in {11..16} do
    lv22tnp[F[index]]:=0;
  end for;
  return lv22tnp;
end function;







//the following fucntion is only used Ros=[0,1,...].
function tnpsq_to_Ros(tnpsq) 
  lm:=(tnpsq[N[0]]*tnpsq[N[8]])/(tnpsq[N[4]]*tnpsq[N[12]]);
  mu:=(tnpsq[N[8]]*tnpsq[N[2]])/(tnpsq[N[12]]*tnpsq[N[6]]);
  nu:=(tnpsq[N[2]]*tnpsq[N[0]])/(tnpsq[N[6]]*tnpsq[N[4]]);
  return [0,1,lm,mu,nu];
end function;



//the following fucntion is only used Ros=[0,1,...].
function lv22tnp_to_Ros(lv22tnp) 
  lm:=((lv22tnp[N[0]]*lv22tnp[N[8]])/(lv22tnp[N[4]]*lv22tnp[N[12]]))^2;
  mu:=((lv22tnp[N[8]]*lv22tnp[N[2]])/(lv22tnp[N[12]]*lv22tnp[N[6]]))^2;
  nu:=((lv22tnp[N[2]]*lv22tnp[N[0]])/(lv22tnp[N[6]]*lv22tnp[N[4]]))^2;
  return [0,1,lm,mu,nu];
end function;



//transforme "lv4 theta null pt" to "lv(2,2) theta null pt".
function lv4tnp_to_lv22tnp(lv4tnp)
  lv22tnp:=AssociativeArray();
  for key in lv22keys do
    sum:=0;
    for beta in {[0,0],[0,1],[1,0],[1,1]} do
      sum+:=(-1)^(key[1]*beta[1]+key[2]*beta[2])*lv4tnp[[key[3]+2*beta[1],key[4]+2*beta[2]]];
    end for;
    lv22tnp[key]:=sum/4;
  end for;
  return lv22tnp;
end function;




//we construct f in [86]p.1970. we call it "ff".
function lv22tnp_to_ff(lv22tnp,R)
  tnp:=lv22tnp;

  ff:=AssociativeArray();

  ff[{1}]:=(-tnp[N[0]]*tnp[N[4]]*tnp[N[6]]*tnp[N[12]])/(R*tnp[N[1]]*tnp[N[3]]*tnp[N[9]]*tnp[N[15]]);

  ff[{2}]:=(-tnp[N[4]]*tnp[N[6]]*tnp[N[12]])/(R*tnp[N[2]]*tnp[N[8]]*tnp[N[15]]);

  ff[{3}]:=(-tnp[N[0]]*tnp[N[6]])/(R*tnp[N[2]]*tnp[N[3]]);

  ff[{4}]:=(tnp[N[4]])/(R*tnp[N[1]]);

  ff[{5}]:=(-tnp[N[0]]*tnp[N[12]])/(R*tnp[N[8]]*tnp[N[9]]);

  ff[{}]:=(-(tnp[N[4]]*tnp[N[6]]*tnp[N[12]])^2)/((R^3)*tnp[N[1]]*tnp[N[2]]*tnp[N[3]]*tnp[N[8]]*tnp[N[9]]*tnp[N[15]]);

  const:=tnp[[0,0,0,0]];
  for A in TakePow({1..5}) do
    if #A eq 2 then 
      ff[A]:=const/tnp[eta[U sdiff ({1..5} diff A)]];
    end if;
  end for;

  return ff;
end function;








//we construct Y_lm.
function Mum_to_Y(Ros,Mumford)
  u:=Mumford[1];  //monic 2-deg.
  v:=Mumford[2];
  //M:=SplittingField(u);
  //Mx<x>:=PolynomialRing(M);
  //u:=Mx!u; 
  //roots:=Roots(u);  ////roots is seqence s.t.#roots=2,  constructed by [root,the multiplicity].
  roots,M:=RootsInSplittingField(u);
  x1:=roots[1][1];
  x2:=roots[2][1];
  y1:=Evaluate(v,x1);
  y2:=Evaluate(v,x2);
  v_Y:=y1*y2;
  
  R<a,b>:=PolynomialRing(M,2);
  h:=y1*(x2-a)*(x2-b)-y2*(x1-a)*(x1-b);

  Y:=AssociativeArray();  
  for ind1 in [1..4] do  //l=ind1, m=ind2.
    for ind2 in [ind1+1..5] do
      numerator_of_Y:=Evaluate(h,[Ros[ind1],Ros[ind2]]);  
      Y[[ind1,ind2]]:=M!numerator_of_Y/(x2-x1);
      Y[[ind2,ind1]]:=Y[[ind1,ind2]];
    end for;
  end for;
  for index in [1..5] do
    Y[[index,index]]:=0;
  end for;
  return Y,v_Y;
end function;  







//we construct Y_lm.
function Mum_to_Y_new(Ros,Mumford)
  u:=Mumford[1];  //monic 2-deg.
  v:=Mumford[2];
  //M:=SplittingField(u);
  //Mx<x>:=PolynomialRing(M);
  //u:=Mx!u; 
  //roots:=Roots(u);  ////roots is seqence s.t.#roots=2,  constructed by [root,the multiplicity].
  roots,M:=RootsInSplittingField(u);
  x1:=roots[1][1];
  x2:=roots[2][1];
  y1:=Evaluate(v,x1);
  y2:=Evaluate(v,x2);
  v_Y:=y1*y2;
  
  R<a,b>:=PolynomialRing(M,2);
  h:=y1*(x2-a)*(x2-b)-y2*(x1-a)*(x1-b);

  Y:=AssociativeArray();  
  for ind1 in [1..4] do  //l=ind1, m=ind2.
    for ind2 in [ind1+1..5] do
      numerator_of_Y:=Evaluate(h,[Ros[ind1],Ros[ind2]]);  
      Y[{ind1,ind2}]:=M!numerator_of_Y/(x2-x1);
    end for;
  end for;
  return Y,v_Y;
end function;  






// we calculate lv(2,2) theta cordinate squread.
function Y_to_lv22tcsq(Y,Ros,Mumford,ff)
  u:=Mumford[1];
  lv22tcsq:=AssociativeArray();   //tcsq=(theta_i(z)/theta_14(z))^2.
  //cf.[86]A.3.  
  lv22tcsq[N[14]]:=1;  
  
  ua:=[];
  for index in {1..5} do  
    ua[index]:=Evaluate(u,Ros[index]);
  end for;

  for index in {1..5} do  
    lv22tcsq[eta[U sdiff {index}]]:=(ua[index]*ff[{}]^2)/ff[{index}]^2;
  end for;

  for index1 in {1..4} do
    for index2 in {(index1+1)..5} do
      lv22tcsq[eta[U sdiff {index1,index2}]]:=(ff[{}]^2*Y[[index1,index2]]^2)/(ff[{index1,index2}]^2*ua[index1]*ua[index2]);
    end for;
  end for;

  return lv22tcsq;
end function;
  




// we calculate lv(2,2) theta cordinate squread.
function Y_to_lv22tcsq_new(Y,Ros,Mumford,ff)
  u:=Mumford[1];
  lv22tcsq:=AssociativeArray();   //tcsq=(theta_i(z)/theta_14(z))^2.
  //cf.[86]A.3.  
  lv22tcsq[N[14]]:=1;  
  ua:=[];
  for index in {1..5} do  
    ua[index]:=Evaluate(u,Ros[index]);
  end for;
  for index in {1..5} do  
    lv22tcsq[eta[U sdiff {index}]]:=(ua[index]*ff[{}]^2)/ff[{index}]^2;
  end for;
  for index1 in {1..4} do
    for index2 in {(index1+1)..5} do
      lv22tcsq[eta[U sdiff {index1,index2}]]:=(ff[{}]^2*Y[{index1,index2}]^2)/(ff[{index1,index2}]^2*ua[index1]*ua[index2]);
    end for;
  end for;
  return lv22tcsq;
end function;
  





//typeに関する準備をする. 
//{1..5}の2点以下の集合の4つの集合に対して, そのTypeと計算するためのリストを返す関数. 

function decide_list(subsets)
  assert (#subsets eq 4);
  cup:=&join[sub :sub in subsets];  //和集合をとった.

  //cup:={};
  //for sub in subsets do
    //cup:=cup join sub;
  //end for;

  assert (#cup ge 2);
  
  if #cup eq 2 then
    return "Type_A",SetToSequence(cup);
  end if;

  if #cup eq 3 then 
    nonemp_seq:={SetToSequence(sub):sub in (subsets diff {{}})};
    return "Type_B",SetToSequence(nonemp_seq),SetToSequence(cup);
  end if;
  
  if #cup eq 5 then

    if #[sub :sub in subsets | #sub eq 1 ] eq 3 then 
      for sub in subsets do
        if #sub eq 2 then 
          return "Type_C",SetToSequence(sub);
        end if;
      end for;
    end if;
    
    if #[sub: sub in subsets | #sub eq 1] eq 1 then 
      for sub in subsets do
        if #sub eq 1 then 
          if &meet[other_sub:other_sub in subsets diff {sub}] eq {} then 
            return "Type_D",[SetToSequence(other_sub) : other_sub in subsets diff {sub}];

          else return "Type_E",[SetToSequence(other_sub):other_sub in subsets diff {sub}],SetToSequence(sub)cat SetToSequence(&meet[other_sub:other_sub in subsets diff {sub}]);
          end if;
        end if;
      end for;
    end if;
  end if;
  return "Error";
end function;




//使わない.
//typeに関する準備をする. 
//{1..5}の2点以下の集合の4つの集合に対して, そのTypeと計算するためのリストを返す関数. 

function decide_list_new(subsets)
  assert (#subsets eq 4);
  cup:=&join[sub :sub in subsets];  //和集合をとった.

  //cup:={};
  //for sub in subsets do
    //cup:=cup join sub;
  //end for;

  assert (#cup ge 2);
  
  if #cup eq 2 then
    return "Type_A",cup;
  end if;

  if #cup eq 3 then 
    nonemp_seq:={SetToSequence(sub):sub in (subsets diff {{}})};
    return "Type_B",nonemp_seq,cup;
  end if;
  
  if #cup eq 5 then

    if #[sub :sub in subsets | #sub eq 1 ] eq 3 then 
      for sub in subsets do
        if #sub eq 2 then 
          return "Type_C",sub;
        end if;
      end for;
    end if;
    
    if #[sub: sub in subsets | #sub eq 1] eq 1 then 
      for sub in subsets do
        if #sub eq 1 then 
          if &meet[other_sub:other_sub in subsets diff {sub}] eq {} then 
            return "Type_D",[other_sub : other_sub in subsets diff {sub}];

          else return "Type_E",
          [SetToSequence(other_sub):other_sub in subsets diff {sub}],SetToSequence(sub)cat SetToSequence(&meet[other_sub:other_sub in subsets diff {sub}]);
          end if;
        end if;
      end for;
    end if;
  end if;
  return "Error";
end function;





//v_Yは論文内のYのこと. 
function term_odd_tc_new(Ros,Y,v_Y,Mumford,subsets)
  Type:=decide_list(subsets);
  u:=Mumford[1];
  ua:=[];
  for index in {1..5} do
    ua[index]:=Evaluate(u,Ros[index]);
  end for;

  if Type eq "Type_A" then 
    _,twopt:=decide_list(subsets);
    return Y[SequenceToSet(twopt)];
  end if;

  if Type eq "Type_B" then
    _,twopts,threept:=decide_list(subsets); 
    value_B:=(Y[SequenceToSet(twopts[1])]*Y[SequenceToSet(twopts[2])]*Y[SequenceToSet(twopts[3])])/(ua[threept[1]]*ua[threept[2]]*ua[threept[3]]);
    return value_B;
  end if;

  if Type eq "Type_C" then
    _,twopt:=decide_list(subsets);
    value_C:=(v_Y*Y[SequenceToSet(twopt)])/(ua[twopt[1]]*ua[twopt[2]]);
    return value_C;
  end if;

  if Type eq "Type_D" then
    _,tripletwo:=decide_list(subsets);
    return (Y[SequenceToSet(tripletwo[1])]*Y[SequenceToSet(tripletwo[2])]*Y[SequenceToSet(tripletwo[3])])/v_Y;
  end if;

  if Type eq "Type_E" then
    _,tritwo,twoel:=decide_list(subsets);
    value_E:=(ua[twoel[1]]*Y[SequenceToSet(tritwo[1])]*Y[SequenceToSet(tritwo[2])]*Y[SequenceToSet(tritwo[3])])/(ua[twoel[2]]*v_Y);
    return value_E;
  end if;

end function;








//v_Yは論文内のYのこと. 
function term_odd_tc(Ros,Y,v_Y,Mumford,subsets)
  Type:=decide_list(subsets);
  u:=Mumford[1];
  ua:=[];
  for index in {1..5} do
    ua[index]:=Evaluate(u,Ros[index]);
  end for;

  if Type eq "Type_A" then 
    _,twopt:=decide_list(subsets);
    return Y[twopt];
  end if;

  if Type eq "Type_B" then
    _,twopts,threept:=decide_list(subsets); 
    value_B:=(Y[twopts[1]]*Y[twopts[2]]*Y[twopts[3]])/(ua[threept[1]]*ua[threept[2]]*ua[threept[3]]);
    return value_B;
  end if;

  if Type eq "Type_C" then
    _,twopt:=decide_list(subsets);
    value_C:=(v_Y*Y[twopt])/(ua[twopt[1]]*ua[twopt[2]]);
    return value_C;
  end if;

  if Type eq "Type_D" then
    _,tripletwo:=decide_list(subsets);
    return (Y[tripletwo[1]]*Y[tripletwo[2]]*Y[tripletwo[3]])/v_Y;
  end if;

  if Type eq "Type_E" then
    _,tritwo,twoel:=decide_list(subsets);
    value_E:=(ua[twoel[1]]*Y[tritwo[1]]*Y[tritwo[2]]*Y[tritwo[3]])/(ua[twoel[2]]*v_Y);
    return value_E;
  end if;

end function;







//c12のとこ.　要確認.

//we want to get (double) lv22tc.
function Mum_to_dbllv22tc(Ros,lv22tnp,Y,v_Y,Mumford,ff,lv22tcsq)
  u:=Mumford[1];
  v:=Mumford[2];
  d_lv22tc:=AssociativeArray(); //wanted.

  //first, we calculate even tc.
  for ab in even_lv22keys do
    term:=AssociativeArray();
    for albe in lv22keys do
      term[albe]:=((-1)^(ab[1]*albe[3]+ab[2]*albe[4]))*lv22tcsq[[(ab[1]+albe[1]) mod 2,(ab[2]+albe[2]) mod 2,(ab[3]+albe[3]) mod 2,(ab[4]+albe[4]) mod 2]]*lv22tcsq[albe];
    end for;
    d_lv22tc[ab]:=(&+[term[albe]:albe in lv22keys])/(4*lv22tnp[ab]*lv22tnp[[0,0,0,0]]^2);
  end for;

  //Second,odd theta.
  temp_4pow:=(ff[{}]^4)*lv22tcsq[eta[{1,3,5}]]^2;

  for ab in odd_lv22keys do
    RHSforab:=AssociativeArray();
    for tup in data_of_ab[ab] do
      subsets:=tup[3];
      sign:=tup[4];
      RHSforab[tup]:=sign*term_odd_tc(Ros,Y,v_Y,Mumford,subsets)/(&*[ff[sub]:sub in subsets]);
    end for;
    d_lv22tc[ab]:=temp_4pow*(&+[RHSforab[tup]:tup in data_of_ab[ab]])/(lv22tnp[[ab[1],ab[2],0,0]]*lv22tnp[[0,0,ab[3],ab[4]]]*lv22tnp[[0,0,0,0]]);
  end for;

  return d_lv22tc;
end function;







//c12のとこ.　要確認.

//we want to get (double) lv22tc.
function Mum_to_dbllv22tc_new(Ros,lv22tnp,Y,v_Y,Mumford,ff,lv22tcsq)
  u:=Mumford[1];
  v:=Mumford[2];
  d_lv22tc:=AssociativeArray(); //wanted.

  //first, we calculate even tc.
  for ab in even_lv22keys do
    term:=AssociativeArray();
    for albe in lv22keys do
      term[albe]:=((-1)^(ab[1]*albe[3]+ab[2]*albe[4]))*lv22tcsq[[(ab[1]+albe[1]) mod 2,(ab[2]+albe[2]) mod 2,(ab[3]+albe[3]) mod 2,(ab[4]+albe[4]) mod 2]]*lv22tcsq[albe];
    end for;
    d_lv22tc[ab]:=(&+[term[albe]:albe in lv22keys])/(4*lv22tnp[ab]*lv22tnp[[0,0,0,0]]^2);
  end for;

  //Second,odd theta.
  temp_4pow:=(ff[{}]^4)*lv22tcsq[eta[{1,3,5}]]^2;

  for ab in odd_lv22keys do
    RHSforab:=AssociativeArray();
    for tup in data_of_ab[ab] do
      subsets:=tup[3];
      sign:=tup[4];
      RHSforab[tup]:=sign*term_odd_tc_new(Ros,Y,v_Y,Mumford,subsets)/(&*[ff[sub]:sub in subsets]);
    end for;
    d_lv22tc[ab]:=temp_4pow*(&+[RHSforab[tup]:tup in data_of_ab[ab]])/(lv22tnp[[ab[1],ab[2],0,0]]*lv22tnp[[0,0,ab[3],ab[4]]]*lv22tnp[[0,0,0,0]]);
  end for;

  return d_lv22tc;
end function;










//PMの選択を追加. PM=[1,1,1,1].
//c12のとこ.　要確認.

//we want to get (double) lv22tc.
function Mum_to_dbllv22tc_PM(Ros,lv22tnp,Y,v_Y,Mumford,ff,lv22tcsq,PM)
  u:=Mumford[1];
  v:=Mumford[2];
  d_lv22tc:=AssociativeArray(); //wanted.

  //first, we calculate even tc.
  for ab in even_lv22keys do
    term:=AssociativeArray();
    for albe in lv22keys do
      term[albe]:=((-1)^(ab[1]*albe[3]+ab[2]*albe[4]))*lv22tcsq[[(ab[1]+albe[1]) mod 2,(ab[2]+albe[2]) mod 2,(ab[3]+albe[3]) mod 2,(ab[4]+albe[4]) mod 2]]*lv22tcsq[albe];
    end for;
    d_lv22tc[ab]:=(&+[term[albe]:albe in lv22keys])/(4*lv22tnp[ab]*lv22tnp[[0,0,0,0]]^2);
  end for;

  //Second,odd theta.
  temp_4pow:=(ff[{}]^4)*lv22tcsq[eta[{1,3,5}]]^2;

  for ab in odd_lv22keys do
    RHSforab:=AssociativeArray();
    cc:=0;
    for tup in data_of_ab[ab] do
      cc:=cc+1;
      pm:=PM[cc];
      subsets:=tup[3];
      sign:=tup[4];
      RHSforab[tup]:=pm*sign*term_odd_tc(Ros,Y,v_Y,Mumford,subsets)/(&*[ff[sub]:sub in subsets]);
    end for;
    d_lv22tc[ab]:=temp_4pow*(&+[RHSforab[tup]:tup in data_of_ab[ab]])/(lv22tnp[[ab[1],ab[2],0,0]]*lv22tnp[[0,0,ab[3],ab[4]]]*lv22tnp[[0,0,0,0]]);
  end for;
  
  return d_lv22tc;
end function;






//By[86]p.1955.
function dbllv22tc_to_lv4tc(dbllv22tc)
  lv4tc:=AssociativeArray();
  ext_dbllv22tc:=ext_chara_lv22(dbllv22tc);
  for key in {[b1,b2]: b1,b2 in {0..3}} do
    lv4tc[key]:=&+[ext_dbllv22tc[[a1,a2,key[1],key[2]]]:a1,a2 in {0,1}];
  end for;
  return lv4tc;
end function;


function const_nY(Y)

  nY:=AssociativeArray();
  for PM in CartesianPower({1,-1},10) do
    nY[PM]:=AssociativeArray();
    nY[PM][[1,2]]:=PM[1]*Y[[1,2]];
    nY[PM][[1,3]]:=PM[2]*Y[[1,3]];
    nY[PM][[1,4]]:=PM[3]*Y[[1,4]];
    nY[PM][[1,5]]:=PM[4]*Y[[1,5]];
    nY[PM][[2,3]]:=PM[5]*Y[[2,3]];
    nY[PM][[2,4]]:=PM[6]*Y[[2,4]];
    nY[PM][[2,5]]:=PM[7]*Y[[2,5]];
    nY[PM][[3,4]]:=PM[8]*Y[[3,4]];
    nY[PM][[3,5]]:=PM[9]*Y[[3,5]];
    nY[PM][[4,5]]:=PM[10]*Y[[4,5]];

    for i1 in {1..4} do
      for i2 in {i1+1..5} do
        nY[PM][[i2,i1]]:=nY[PM][[i1,i2]];
      end for;
    end for;
  end for;
  
  return nY;
end function; 




//最終version.
//R=one of sqrt of (a_2-a_1).

function Div_to_lv4tc(lv22tnp,D: R:=1)
  u:=D[1];
  v:=D[2];
  Mumford:=[u,v];
  Ros:=lv22tnp_to_Ros(lv22tnp);
  Y,v_Y:=Mum_to_Y(Ros,Mumford);
  nY:=const_nY(Y);
  PM10:=<1, 1, -1, 1, 1, 1, -1, 1, -1, -1>;
  ff:=lv22tnp_to_ff(lv22tnp,R);
  lv22tcsq:=Y_to_lv22tcsq(Y,Ros,Mumford,ff);
  dbllv22tc:=Mum_to_dbllv22tc(Ros,lv22tnp,nY[PM10],v_Y,Mumford,ff,lv22tcsq);
  lv4tc:=dbllv22tc_to_lv4tc(dbllv22tc);
  return lv4tc;
end function;





//End of Mum_to_theta7
//==================================================

