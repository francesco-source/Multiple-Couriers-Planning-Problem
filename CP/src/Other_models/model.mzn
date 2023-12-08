include "alldifferent.mzn";
include "globals.mzn";


int: courier; 
int: items; 
int: up_bound;
int: min_load;
int: max_load;
int :low_bound;
int :d_low_bound;
int : ratio_packages;

set of int: COURIERS = 1..courier;
set of int: ITEMS = 1..items;
set of int: NODES = 1..items + 1;


int: package = (items div (courier -1)) + 1 + 3;

set of int: PACKAGES = 1..package;

array[COURIERS] of int: courier_size; % maximum load size for each courier, l
array[ITEMS] of int: item_size; % size of each item, s
array[NODES, NODES] of int: distances; % distance matrix, d

array[COURIERS, PACKAGES] of var NODES: x;
array[COURIERS] of var d_low_bound..up_bound: m_dist;

array[ITEMS] of var COURIERS: loads; %PRIMA C'ERA SCRITTO 0..courier
array[COURIERS] of var min_load..max_load: couriers_loads;


%ogni items deve essere presente solo una volta
constraint forall(i in ITEMS)(count(x,i,1))::domain;

%elementi prima di items+1 tutti diversi da items+1
constraint forall(i in COURIERS, j in PACKAGES where x[i, j] != items + 1)( 
  forall(k in 1..j - 1)(
    x[i, k] != items + 1  
  )
)::domain;

% se è già presente un ritorno alla base
% allora gli elementi successivi devono essere tutti n+1
constraint forall(i in COURIERS, j in PACKAGES where x[i, j] == items + 1)(
  forall(k in j+1..package)(
    x[i, k] == items + 1  
  )
)::domain;

% all the couriers must start
constraint forall(i in COURIERS)(x[i,1] != items+1)::domain;

 
%load limit constraint
constraint forall(k in COURIERS)(forall(i in PACKAGES)(if x[k,i] != items+1 then loads[x[k,i]] == k endif))::domain;

constraint bin_packing_capa(courier_size,loads,item_size)::domain;

% Symmetry breaking constraint
constraint forall(k in COURIERS)(
    couriers_loads[k] = sum(
            [item_size[i] | i in ITEMS where loads[i] == k]))::domain;
            
            
%calculate the distances
constraint forall(i in COURIERS)(m_dist[i] = distances[items+1,x[i,1]] + 
sum(j in 1..package-1)(distances[x[i,j], x[i,j+1]]) + distances[x[i,package],items+1])::domain;

var low_bound..up_bound: rho;
%var low_bound..up_bound: maximum = max(m_dist);
constraint forall(i in COURIERS)(rho >= m_dist[i])::domain;

solve :: seq_search([
                int_search(x, first_fail, indomain_min),
                int_search(loads, first_fail, indomain_min)])
                minimize(rho)::domain;
     
     
