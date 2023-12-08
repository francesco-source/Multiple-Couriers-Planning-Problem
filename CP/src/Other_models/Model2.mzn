include "alldifferent.mzn";
include "globals.mzn";

int: m; % number of couriers
int: n; % number of items
array[1..m] of int: l; % maximum load size for each courier
array[1..n] of int: s; % size of each item
array[1..n+1, 1..n+1] of int: D; % distance matrix

int: MAX_D = max(D)*(n+1);
int: MIN_D = min(D);

array[1..m,1..n+1] of var 0..n: x;
array[1..m] of var MIN_D..MAX_D: m_dist;

constraint forall(i in 1..n)(count(j in x)(j==i) == 1)::domain;

constraint forall(i in 1..m)(sum(j in 1..n+1 where x[i,j] !=0)(s[x[i,j]]) <= l[i])::domain;

% constraint alldifferent([x[i,j] | i in 1..m, j in 1..n+1 where x[i,j]!=0])::domain;

% Simmetry breaking between two correers that have the same load size.
constraint forall(i, j in 1..m where i < j /\ l[i] == l[j])(
  lex_lesseq([x[i,k] | k in 1..n+1], [x[j,k] | k in 1..n+1]))::domain;

%Forziamo ogni corriere a depositare un total load maggiore o uguale ad un corriere che ha un uguale o minore possibilità di carico)
constraint forall(i,j in 1..m where i<j /\ l[i]>= l[j])(
  sum(k in 1..n+1 where x[i,k] != 0)(s[x[i,k]]) >=
  sum(k in 1..n+1 where x[j,k] != 0)(s[x[j,k]])
)::domain;

%calculate the distances
constraint forall(i in 1..m)(
  let {
    var int: counter = count(j in 1..n+1)(x[i,j]!=0);
  } in
  if counter != 0 then
    m_dist[i] = (D[n+1,x[i,1]] + D[x[i,counter], n+1]) + sum(j in 1..counter-1)(D[x[i,j], x[i,j+1]])
  else
    m_dist[i] = 0
  endif
)::domain;

var int: dist_squared = max(m_dist);

solve :: int_search(x, first_fail,indomain_random) minimize dist_squared;
