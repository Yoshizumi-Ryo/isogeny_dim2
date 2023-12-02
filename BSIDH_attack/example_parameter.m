
function smooth(p,max_l)
  facseq_p:=fatoriztion_seq(p+1);
  facseq_m:=fatoriztion_seq(p-1);
  Np:=1;
  Nm:=1;

  for i in {1..#facseq_p} do
    if facseq_p[i] le max_l then
      Np*:=facseq_p[i];
    end if;
  end for;

  for i in {1..#facseq_m} do
    if facseq_m[i] le max_l then
      Nm*:=facseq_m[i];
    end if;
  end for;

  N_A:=Max(Np,Nm);
  N_B:=1;

  if Np eq N_A then
    for i in {1..#facseq_m} do
      if N_B*facseq_m[i] le N_A then
        N_B*:=facseq_m[i];
      else
        break i;
      end if;
    end for;
  end if;
  
  if Nm eq N_A then
    for i in {1..#facseq_p} do
      if N_B*facseq_p[i] le N_A then
        N_B*:=facseq_p[i];
      else
        break i;
      end if;
    end for;
  end if;

  assert(N_A gt N_B);
  a:=N_A-N_B;
  if a*N_B le p then
    return false;
  end if;
  return true,N_A,N_B;
end function;

  
procedure compute_prime(min_p,max_p,max_l)
  for q in {min_p..max_p} do
    if IsPrime(q) and (q mod 4 eq 3) then
      if smooth(q,max_l) then
        _,N_A,N_B:=smooth(q,max_l);
        //if not(IsDivisibleBy(N_A,4)) then
          "prime",q,
          "N_A",fatoriztion_seq(N_A);
          N_B;
          break q;
          //fatoriztion_seq(N_B);
          "";
        //end if;
      end if;
    end if;
  end for;
end procedure;


compute_prime(10^6,2*10^6,30);

compute_prime(2^250,2^250+10^4,2^100);
      
//----------------------------------------

p:=991;
N_A:=3^2*5*11;
N_B:=2^5;


p:=911;
N_A:=5*7*13;
N_B:=2^4*3;



p:=859;
N_A:=3*11*13;
N_B:=2^2*5;

p:=11287;
N_A:=3^3*11*19;
N_B:=136;



p:=14951;
N_A:=5^2*13*23;
N_B:=168;


p:=104959;
N_A:= 3^2 * 7^3 * 17;
N_B:=2^9 * 5;

p:=1479871;
N_A:=3^6*5*7*29;
N_B:=1216;


p:=202546499;
N_A:=7^2 * 11^2 * 19 * 29 * 31;
N_B:=2^2 * 3 * 5^3 * 13^2 * 17;


p:=0x76042798BBFB78AEBD02490BD2635DEC131ABFFFFFFFFFFFFFFFFFFFFFFFFFFF;
N_A:=3^(34)*11*17*19^2*53^2*97*107*109*131*137*197*199*227;
N_B:=2^110*5*7^2;



p:=2^32*5^21*7*11*163*1181*2389*5233*8353*10139*11939*22003*25391*41843*3726787*6548911-1;
N_A:=3^56;
N_B:=2^32*5^21*7*11;



//------------------------
Ilog2(p);
assert(p mod 4 eq 3);
assert(N_A gt N_B);
assert((N_A-N_B)*N_B gt p);
//-------------------------
