# isogeny_dim2

次の順番で読み込ませてください. (Please import the following order.)
標数pは1の一番最初のところで決めてください.

1.setting3.m (全体的な補助関数やprecomputation) [標数pのみここで設定]

2.func_addition8.m (2次元level4thetaの加法に関わる関数集)

3.func_isogeny3.m (2次元level4の同種写像の計算に関わる関数集)

4.func_elliptic_theta4.m  (楕円曲線上のthetaに関わる関数集)

5.func_theta_trans.m (2次元level4のtheta transformationに関わる関数)

6.func_torsion_attack6.m  (SIDH-attackに関する関数集)

7.test_setting_attack.m  (SIDH-attackの実装コード) [他のパラメータはここで設定]

--------------------
func_Mum_to_theta (Mumford表現とtheta座標の間の変換に関わる関数) [上の1の後にimportしてください.]
