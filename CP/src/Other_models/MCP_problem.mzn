include "globals.mzn";

% Use this editor as a MiniZinc scratch book
% Define input parameters
int: m; % number of couriers
int: n; % number of items
array[1..m] of int: l; % maximum load size for each courier
array[1..n] of int: s; % size of each item
array[1..n+1, 1..n+1] of int: D; % distance matrix

array[1..m, 1..n] of var bool: x;% 1 if the element is carried by the coreer , 0 if the element is not carried
array[1..m] of var 0..n: num_obj;
array [1..m , 1..n] of var 0..n: order_motion;
array[1..m] of var int: m_dist;

% each item must be assigned only once.
constraint forall(j in  1..n)(sum(i in 1..m) (x[i,j]) == 1);

% we cannot exceed the weight of a correer.
constraint forall(i in  1..m)(sum(j in 1..n)(s[j]*x[i,j]) <= l[i]);

% i pacchi 1..n compaiono solo una volta in order motion una sola volta ogni elemento.
constraint forall(i in 1..n)( count(j in order_motion)(j==i) == 1 );

% num_obj è il numero di pacchi che porta ogni corriere.
constraint forall(i in 1..m)(num_obj[i] == sum(j in 1..n)(x[i,j]));

% in order_motion gli elementi che non sono pacchi devono essere zeri
constraint forall(i in 1..m, j in 1..n where j > num_obj[i]) (order_motion[i, j] == 0);

constraint forall(i in 1..m, idx in 1..n where order_motion[i,idx] != 0) (x[i, order_motion[i, idx]] != 0) ;

% il vettore m_dist è definito essere la somma delle distanze che compongono la sequenza
constraint forall(i in 1..m  where num_obj[i] > 0)(m_dist[i] == (D[ n+1 , order_motion[i,1] ] +  D[order_motion[i, num_obj[i]] , n + 1 ]+
                             sum(j in 1..num_obj[i]-1)(D[order_motion[i,j],order_motion[i , j+1]])));

constraint forall(i in 1..m  where num_obj[i] == 0) (m_dist[i] == 0);


var int: dist_squared = sum(i in 1..m)(m_dist[i]*m_dist[i]);

solve minimize dist_squared;