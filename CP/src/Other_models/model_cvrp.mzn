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


array[COURIERS] of int: courier_size; 
array[ITEMS] of int: item_size; 
array[NODES, NODES] of int: distances; 

array[NODES, NODES, COURIERS] of var 0..1: x;

array[COURIERS, NODES] of var opt NODES: order;

array[COURIERS] of var d_low_bound..up_bound: m_dist;

var low_bound..up_bound: rho;

array[ITEMS] of var COURIERS: loads; 


%CONSTRAINTS FOR VARIABLE X
constraint forall(j in NODES, k in COURIERS)(sum(i in NODES)(x[i,j,k]) == sum(i in NODES)(x[j,i,k]));
constraint forall(j in ITEMS)(sum(i in NODES, k in COURIERS)(x[i,j,k]) == 1);
constraint forall(i in ITEMS)(sum(j in NODES, k in COURIERS)(x[i,j,k]) == 1);
constraint forall(i in NODES, k in COURIERS)(x[i,i,k] == 0);
constraint forall(k in COURIERS)(sum(j in ITEMS)(x[items+1,j,k]) == 1);


%SUBTOUR ELIMINATION
constraint forall(i in NODES, j in NODES, k in COURIERS)(if x[i,j,k]==1 then order[k,i]==j endif);
constraint forall(k in COURIERS)(circuit([order[k,i] | i in NODES]));


%LOAD CONSTRAINT
constraint forall(k in COURIERS, i in NODES, j in ITEMS)(if order[k,i]==j then loads[j]==k endif);
constraint bin_packing_capa(courier_size,loads,item_size);


%DISTANCE COMPUTATION
constraint forall(k in COURIERS)(m_dist[k] == sum(j in NODES, i in NODES)(distances[i,j]*x[i,j,k]));


%CONSTRAINT FOR OBJECTIVE VARIABLE
constraint forall(k in COURIERS)(rho >= m_dist[k]);

  
solve :: seq_search([
                int_search(x, first_fail, indomain_min)
                ])
     minimize(rho);

