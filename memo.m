//magmaの全般的なメモ. 



//===================================================
//多項式に代入する方法
K=GF(11);
Kx<x>:=PolynomialRing(K);
u:=x^3+4*x^2+2*x+1;
cu1:=Coefficient(u,2);   //これはx^2の係数を与える. 
vu1:=Evaluate(u,6);    //これはuにx=6を代入したものを与える.





//===================================================
//多変数多項式に代入する方法
K=GF(11);
Kx<x,y>:=PolynomialRing(K,2);
f:=x+y;
value:=Evaluate(f,[1,4]); 





//===================================================
//4変数a,b,x,yで与えられた多項式fをa,bに関して整理する方法. 
K:=GF(11);
R<x,y>:=PolynomialRing(K,2);
S<a,b>:=PolynomialRing(R,2);
f:=a*b*x^4*y^2+a*b*x^2+a^2*(4+b)*y+1;
f;




//===================================================
//多変数多項式の係数を見る方法
K:=GF(101);
R<x,y>:=PolynomialRing(K,2);
f:=3*x^6*y+4+2*x^5*y^5;
f;  //これをするとfをx,yの次数の辞書式順序で並べてくれる. 
c:=Coefficients(f);   //cは順序付き列. 
c[1];  //結果は3. 次数が小さい順に教えてくれる. 





//===================================================
//次数が分かっていない1変数多項式の係数を見る方法.(多変数に拡張可能).
K:=GF(101);
Kx<x>:=PolynomialRing(K);
f:=3*x^3+6*x^2;  //定数関数だとエラー起こす. 
c:=Coefficients(f);
d:=#c-1;






//===================================================
//多項式の根をとる (体拡大をいっきにする)
K:=GF(3);
Kx<x>:=PolynomialRing(K);
r,L:=RootsInSplittingField(x^2-2);  //Lも欲しいとき. 
r:=RootsInSplittingField(x^2-2);    //Lはいらないとき.
/*
result
r;
[ <K.1^2, 1>, <K.1^6, 1> ]  //tupleのsequence.
K;
Finite field of size 3^2
*/





//===================================================
//上の続き, n次多項式の根全体を#=nのsequenceにする. 
function root_to_seq(r)
  roots:=[];  //wanted.
  k:=#r; //k is the number of roots ignoering mult.
  for i in [1..k] do
    m:=r[i][2];   //"m" is multipicictiy of r[i][1].
    R:=#roots;
    for j in [R+1..R+m] do
      roots[j]:=r[i][1];
    end for;
  end for;
  return roots;
end function;

















//===================================================
//(上のを使え,これは使わない)
//多項式の根を列挙する方法
K:=GF(3,2);
Kx<x>:=PolynomialRing(K);
f:=x^9-x; //このfはK内には全ての根を持たないので, 体拡大をしておく.  
L:=SplittingField(f);
Lx<x>:=PolynomialRing(L);
f:=Lx!f; 
roots:=Roots(f);  //このrootは[根,重複度]の形のリスト. 






//===================================================
//Define projective space.
K:=GF(7,2);
P2:=ProjectiveSpace(K,2);
P:=P2![1,1,1];   //(1,1,1) in P^2_K.







//===================================================
//多項式の因数分解
K:=GF(3);
Kx<x>:=PolynomialRing(K);
f:=x^2-2;  
L:=SplittingField(f);
Lx<x>:=PolynomialRing(L);
factors := Factorization(Lx!f); 
/*
result
factors;
[ <x + L.1^2, 1>, <x + L.1^6, 1> ]
*/





//===================================================
///forループの進度を見る. 
Anyset:={1..100000}  //any set.
for x in Anyset do
  y:=x+1;
  if 
end for;


  

//===================================================  
//recformat とは. 

1.recoformatを作る. 
2.そのformatに従って具体的なものを作る. 

RF1:=recformat< n : Integers(), misc, seq : SeqEnum >;
RF2:=recformat<name1,name2,Integers()>;  //これはエラー.categoryだけではエラー, 名前は必ず必要. 
RF3:=recformat<name1:Integers(),name2,name3>;

A1:=rec<RF3|name1:=3,name2:="hello",name3:=10>;

A2:=rec<RF3|name2:="hello">;   //部分的にのみ格納することも可能. 

A3:=rec<RF3|name3:="hello",name1:=0>;   //順番は何でも良い. 
  
A4:=rec<RF3|name1:="hello">;  //これはエラー.

//A3のname1の値を見るには?

A3`name1;   //とする. 

A3`name2;   //は定義されてないのでエラー. 






//===================================================
//有限アーベル群の構成方法, 扱い方


//Z/2Z+Z/3Z+Z/4Z+Z/5Z+Z/6Z+Z+Z.

G:=AbelianGroup([2,3,4,5,6,0,0]);    

Invariants(G); 
//[ 2, 6, 60, 0, 0 ]

g:=Random(G); 

Eltseq(g);

Z2:=AbelianGroup([2,2]);

Ab_22:=AbelianGroup([2,2]);

Invariants





//===================================================
//Assocの成分がAssocのときの注意. 

A:=AssociativeArray();
A[1]:=AssociativeArray();
A[1]["hello"]:=2;

//次の2つは同じ意味. 
B:=A[1,"hello"];
B:=A[1]["hello"];



//===================================================
//returnとして2つ返す. 

function hoge(n)
  m:=n+1;
  l:=n+2;
  return m,l;
end function;

p,q:=hoge(3);
p;
//4
q;
//5

//第1成分のみ欲しい場合. 
p:=hoge(4);

//第2成分のみ欲しい場合. 
_,q:=hoge(4);


//===================================================
//関数の引数としてあらかじめ設定. 

//固定する引数の前は,でなく:を使う. 
function test(m: n:=3)
  l:=m+n;
  return l;
end function;

//特に指定しないとn=3が使われる. 
> test(100);
103

//以下のように書けば, n=3でないようにも出来る. 
> test(100: n:=50);   
150






//===================================================
//procedureとは.

want:=AssociativeArray();

procedure hoge(a,~AA) 
  AA["test"]:=a;
end procedure;

hoge(100,~want);

//result.
> want["test"];
100



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





//_______________________________
//3個以上のカルテシアン積を構成. 

A:={1,2,3};
B:={1,2,4};
C:={3,5,6};

X:=CartesianProduct([A,B,C]);



//_______________________________
//asso arrayを羅列する関数.

procedure expr(A)
  for key in Keys(A) do
    key;
    A[key];
    "";
  end for;
end procedure;




//_______________________________
//和を一度にとる. 

AA:=[];
for num in {1..10} do
  AA[num]:=2^num;
end for;

//AA[4]=16.

S:={3,5,8};
sum:=&+[AA[num]:num in S];


sum:=&+[AA[num]:num in {1..10}|IsPrime(num)];
//2^2+2^3+2^5+2^7.


//&+の後は配列にする!!.集合にしたら同じものが消えて一回しかカウントされない!.



