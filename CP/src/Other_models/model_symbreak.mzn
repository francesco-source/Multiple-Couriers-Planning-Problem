include "alldifferent.mzn";
include "globals.mzn";

int: courier; 
int: items; 
int: up_bound;
int: min_load;
int: max_load;
int :low_bound;
int :d_low_bound;

set of int: COURIERS = 1..courier;
set of int: ITEMS = 1..items;
set of int: NODES = 1..items + 1;

array[COURIERS] of int: courier_size; % maximum load size for each courier, l
array[ITEMS] of int: item_size; % size of each item, s
array[NODES, NODES] of int: distances; % distance matrix, d


array[COURIERS, NODES] of var NODES: x;
array[COURIERS] of var d_low_bound..up_bound: m_dist;


array[ITEMS] of var COURIERS: loads; %PRIMA C'ERA SCRITTO 0..courier
array[COURIERS] of var min_load..max_load: couriers_loads;

var low_bound..up_bound: rho;

%ogni items deve essere presente solo una volta
constraint forall(i in ITEMS)(count(x,i,1));

%elementi prima di items+1 tutti diversi da items+1
constraint forall(i in COURIERS, j in ITEMS where x[i, j] != items + 1)(
  forall(k in 1..j - 1)(
    x[i, k] != items + 1  
  )
);

%se è già presente un ritorno alla base
% allora gli elementi successivi devono essere tutti n+1
constraint forall(i in COURIERS, j in ITEMS where x[i, j] == items + 1)(
  forall(k in j+1..items+1)(
    x[i, k] == items + 1  
  )
)::domain;

% all the couriers must start
constraint forall(i in COURIERS)(x[i,1] != items+1)::domain;

%load limit constraint
constraint forall(k in COURIERS)(forall(i in ITEMS)(if x[k,i] != items+1 then loads[x[k,i]] == k endif));
constraint bin_packing_capa(courier_size,loads,item_size);


% Simmetry breaking between two couriers that have the same load size.
%constraint forall(i, j in COURIERS where i < j /\ courier_size[i] == courier_size[j])(
%  lex_lesseq([x[i,k] | k in NODES], [x[j,k] | k in NODES]));
constraint forall(i, j in COURIERS where i < j /\ couriers_loads[i] <= courier_size[j] /\ couriers_loads[j]<= courier_size[i])(
  lex_lesseq([x[i,k] | k in NODES], [x[j,k] | k in NODES]));
    

  
% Symmetry breaking constraint
constraint forall(k in COURIERS)(
    couriers_loads[k] = sum(
            [item_size[i] | i in ITEMS where loads[i]==k]));
            
% sub tour elimination, if the last courier can carry all the packages then all courier must start
%constraint forall(k in COURIERS) (
  %if courier_size[courier] >= max(item_size) then 
  %exists(j in ITEMS) (x[k,j]!= items+1)  
  %endif);

%calculate the distances
constraint forall(i in COURIERS)(m_dist[i] = distances[items+1,x[i,1]] + sum(j in ITEMS)(distances[x[i,j], x[i,j+1]]))::domain;


%var low_bound..up_bound: maximum = max(m_dist);
constraint forall(i in COURIERS)(rho >= m_dist[i])::domain;

solve :: seq_search([
                int_search(x, first_fail, indomain_min),
                int_search(loads, first_fail, indomain_min)])
 
     minimize(rho);
     

