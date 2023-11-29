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
set of int: START_NODES_PREPATH = items + 2..items + couriers;
set of int: END_NODES = items + couriers + 1..items+ 2 * couriers;
set of int: END_NODES_PATH = items + couriers + 1..items+ 2 * couriers - 1;
set of int: LOADS = 0..max(courier_capacity);


array[NODES] of var NODES: path;
array[NODES] of var NODES: prepath;
array[NODES] of var COURIERS: vehicle_route;
array[NODES] of var 0..up_bound: incremental_dist;

% --- 
constraint circuit(path);
constraint circuit(prepath);

% the end of courier i is connected to the start of courier i+1 and vice versa
constraint forall(i in END_NODES_PATH)(path[i] = i - couriers + 1);
constraint forall(i in START_NODES_PREPATH)(prepath[i] = i + couriers - 1);

% connect the end of the last courier with the start of the first and vice versa
constraint    path[items + 2 * couriers] = items + 1;
constraint prepath[items + 1] = items + 2 * couriers;

% the successor of the predecessor is itself and vice versa
constraint forall(i in NODES) ((path[prepath[i]] == i) /\ (prepath[path[i]] == i));

% all start
constraint forall(i in START_NODES)(path[i] != path[i+couriers]);
constraint forall(i in END_NODES)(prepath[i] != prepath[i-couriers]);

% enforce
constraint forall(i in START_NODES)(vehicle_route[i] = i - items);
constraint forall(i in END_NODES)  (vehicle_route[i] = i - items - couriers);
constraint forall(i in ITEMS)      (vehicle_route[path[i]] = vehicle_route[i]);
constraint forall(i in ITEMS)      (vehicle_route[prepath[i]] = vehicle_route[i]);

constraint bin_packing_capa(courier_capacity,[vehicle_route[i] | i in ITEMS],item_size);

% calculate distance incrementally
constraint forall(i in START_NODES)(incremental_dist[i] = 0);
constraint forall(i in START_NODES)(incremental_dist[path[i]] = distances[items + 1, path[i]]);   % dep->path[i]
constraint forall(i in ITEMS)(incremental_dist[path[i]] = incremental_dist[i] + distances[i, min([path[i], items+1])]);

var low_bound..up_bound: rho;
constraint rho = max(incremental_dist);

solve :: seq_search([
                int_search(path, first_fail, indomain_split),
                int_search(vehicle_route, first_fail, indomain_split),
                int_search(prepath,first_fail,indomain_split),
                %int_search(prepath,first_fail,indomain_min),
                %relax_and_reconstruct(prepath,90),
                %relax_and_reconstruct(path, 90),
                %restart_luby(items)
                ])
                minimize(rho)::domain;