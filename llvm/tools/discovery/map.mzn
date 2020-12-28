% MiniZinc model for finding maps.

include "partition_set.mzn";
include "disjoint.mzn";
include "increasing.mzn";

include "common.mzn";

%%% AUXILIARY DEFINITIONS

% Number of non-control nodes. This can be used as an upper bound on the number
% of map runs (setting m = nnc below).
% TODO: a potentially stronger bound would be the maximum number of nodes that
% are not weakly connected.
int: nnc = card({j | i in 0..c-1, j in static_classes[i]
                 where not (i in branches)});

% Upper bound on number of map runs.
int: m = n;

% Set of potential map runs.
set of int: runs = 0..m-1;

%%% VARIABLES

% M is the set of nodes in the map pattern.
var set of nodes: M;

% Mc is the complement of M (nodes not in the map pattern).
var set of nodes: Mc;

% R[i] is the set of nodes of run i in the map.
array[runs] of var set of nodes: R;

% Run[j] is the run of node j (or m if j does not belong to M).
array[nodes] of var 0..m: Run;

% Last run in the map.
var runs: Last;

% Count[k] is the number of nodes that correspond to instruction k in a
% map run.
%
% These variables and the corresponding constraints enforce, by construction,
% that all runs contain the same number of nodes and cover the same
% instructions the same number of times. This is an approximation to run
% isomorphism, which is doable but would add a lot of model overhead (the
% isomorphism bijection would have to be modeled explicitly, as there are no
% global constraints available).
array[insts] of var 0..n: Count;

%%% CONSTRAINTS

constraint map(M, Mc, R, Run, Last, Count);

constraint static_covering(M);

constraint minimum_components(R, 2);

% Enforce run ordering by minimum node, for symmetry breaking.
constraint
increasing([if card(R[i]) > 0 then min(R[i]) else n + 1 endif | i in runs]);

%%% SOLVER SPECIFICATION

solve satisfy;

output ["map: "] ++ [ show(R[i]) ++ " " | i in runs ];
