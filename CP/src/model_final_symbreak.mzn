include "globals.mzn";

int: couriers;
int: items;
array[COURIERS] of int: courier_capacity; % maximum load size for each courier, l
array[ITEMS] of int: item_size; % size of each item, s
array[1..items+1, 1..items+1] of int: distances; % distance matrix, d
int: low_bound;
int: up_bound;
int: sym;

set of int: COURIERS = 1..couriers;      % vehicles
set of int: COURIERS_SYM = 1..couriers - 1;
set of int: ITEMS = 1..items;           % customers
set of int: NODES = 1..items + 2*couriers;
set of int: START_NODES = items + 1..items + couriers;
set of int: START_NODES_PRED = items + 2..items + couriers;
set of int: END_NODES = items + couriers + 1..items+ 2 * couriers;
set of int: END_NODES_SUCC = items + couriers + 1..items+ 2 * couriers - 1;
set of int: LOADS = 0..max(courier_capacity);


array[NODES] of var NODES: successor;
array[NODES] of var NODES: predecessor;
array[NODES] of var COURIERS: courier_route;
array[NODES] of var 0..up_bound: incremental_dist;

% --- 
constraint circuit(successor);
constraint circuit(predecessor);

% the end of courier i is connected to the start of courier i+1 and vice versa
constraint forall(i in END_NODES_SUCC)(successor[i] = i - couriers + 1);
constraint forall(i in START_NODES_PRED)(predecessor[i] = i + couriers - 1);

% connect the end of the last courier with the start of the first and vice versa
constraint    successor[items + 2 * couriers] = items + 1;
constraint predecessor[items + 1] = items + 2 * couriers;

% the successor of the predecessor is itself and vice versa
constraint forall(i in NODES) ((successor[predecessor[i]] == i) /\ (predecessor[successor[i]] == i));

% all start
constraint forall(i in START_NODES)(successor[i] != i+couriers);
constraint forall(i in END_NODES)(predecessor[i] != i-couriers);

% enforce
constraint forall(i in START_NODES)(courier_route[i] = i - items);
constraint forall(i in END_NODES)  (courier_route[i] = i - items - couriers);
constraint forall(i in ITEMS)      (courier_route[successor[i]] = courier_route[i]);
constraint forall(i in ITEMS)      (courier_route[predecessor[i]] = courier_route[i]);

constraint bin_packing_capa(courier_capacity,[courier_route[i] | i in ITEMS],item_size);

constraint forall(i in START_NODES where sym == 1)(successor[i] <= predecessor[i + couriers]);

% calculate distance incrementally
constraint forall(i in START_NODES)(incremental_dist[i] = 0);
constraint forall(i in START_NODES)(incremental_dist[successor[i]] = distances[items + 1, successor[i]]);   % dep->successor[i]
constraint forall(i in ITEMS)(incremental_dist[successor[i]] = incremental_dist[i] + distances[i, min([successor[i], items+1])]);

var low_bound..up_bound: rho;
constraint rho = max(incremental_dist);

solve :: seq_search([
                int_search(successor, first_fail, indomain_split),
                int_search(courier_route, first_fail, indomain_split),
                int_search(predecessor,first_fail,indomain_split),
                %int_search(predecessor,first_fail,indomain_min),
                %relax_and_reconstruct(predecessor,90),
                %relax_and_reconstruct(successor, 90),
                %restart_luby(items)
                ])
                minimize(rho)::domain;