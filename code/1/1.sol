=========================[ Solutions ]=========================
Adding constraint "X_I mod 2 = 0" for values:
	I=1, 
	I=2, 
	I=3, 
	I=4, 
Adding constraint "Y_I mod 2 = 1" for values:
	I=1, 
	I=2, 
	I=3, 
	I=4, 
	I=5, 
	I=6, 
Adding constraint "X_I + Y_I = Y_J + 10 * Z_I" for values:
	I=1, I=1, J=2, I=1, 
Adding constraint "Z_I + X_J + Y_K = X_K + 10*Z_J" for values:
	I=1, J=2, K=3, K=3, J=2, 
Adding constraint "Z_I + Y_J + X_J  =Y_K + 10*Y_L" for values:
	I=2, J=4, J=4, K=5, L=6, 
Backtracks: 4
Runtime: 0.0s
[X,Y,Z] = [[6,2,4,6],[5,1,1,5,1,1],[1,0]]
Backtracks: 0
Runtime: 0.0s
[X,Y,Z] = [[6,2,6,6],[5,1,3,5,1,1],[1,0]]
Backtracks: 0
Runtime: 0.0s
[X,Y,Z] = [[6,4,6,6],[5,1,1,5,1,1],[1,0]]
=======================[ End Solutions ]=======================
