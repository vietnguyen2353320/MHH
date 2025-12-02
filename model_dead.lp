\ ILP Dead Marking via state equation
Minimize
 obj: 0 M_p1
Subject To
 se_p1: M_p1 + 1 x_t1 = 1
 se_p2: M_p2 - 1 x_t1 = 0
 se_pX: M_pX = 0
 dis1_t1:  s_p1_t1 >= 1
 dis2_p1_t1: M_p1 + 1 s_p1_t1 <= 1
 dis1_t_dummy:  s_pX_t_dummy >= 1
 dis2_pX_t_dummy: M_pX + 1 s_pX_t_dummy <= 1
Bounds
 0 <= M_p1 <= 1
 0 <= M_p2 <= 1
 0 <= M_pX <= 1
 x_t1 >= 0
 x_t_dummy >= 0
Binaries
 s_p1_t1
 s_pX_t_dummy
Generals
 x_t1
 x_t_dummy
 M_p1
 M_p2
 M_pX
End
