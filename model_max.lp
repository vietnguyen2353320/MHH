\ ILP Maximize c^T M via state equation
Maximize
 obj: 0
Subject To
 se_P1: M_P1 = 1 - 1 x_T1 + 1 x_T3 - 1 x_T4
 se_P2: M_P2 = 1 - 1 x_T2 - 1 x_T3 + 1 x_T4
 se_P3: M_P3 = 0 + 1 x_T1 - 1 x_T3 + 1 x_T4
 se_P4: M_P4 = 0 + 1 x_T2 + 1 x_T3 - 1 x_T4
Bounds
 0 <= M_P1 <= 1
 0 <= M_P2 <= 1
 0 <= M_P3 <= 1
 0 <= M_P4 <= 1
 x_T1 >= 0
 x_T2 >= 0
 x_T3 >= 0
 x_T4 >= 0
Generals
 x_T1
 x_T2
 x_T3
 x_T4
 M_P1
 M_P2
 M_P3
 M_P4
End
