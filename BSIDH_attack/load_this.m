//please load this file.

load "setting.m";  
load "func_additions.m";
load "func_isogeny.m";
load "func_elliptic_theta.m";
load "func_theta_trans.m";
load "func_torsion_attack.m";
//--------------------------

//input p,N_A,N_B here.


p:=0x76042798BBFB78AEBD02490BD2635DEC131ABFFFFFFFFFFFFFFFFFFFFFFFFFFF;
N_A:=3^(34)*11*17*19^2*53^2*97*107*109*131*137*197*199*227;
N_B:=2^110*5*7^2;


load "test_BSIDH_attack.m"; 
