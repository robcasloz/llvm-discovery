% MiniZinc model for finding linear map-reductions.

include "partition_set.mzn";
include "disjoint.mzn";

include "common.mzn";

%%% AUXILIARY DEFINITIONS

% Upper bound on number of map runs and reduction steps.
int: m = n div 2;

% Set of potential map runs.
set of int: runs = 0..m-1;

% Set of potential reduction steps.
set of int: steps = 0..m-1;

%%% VARIABLES

% MapR is the set of nodes in the linear map-reduction.
var set of nodes: MapR;

% MapRc is the complement of MapR (nodes not in the linear map-reduction).
var set of nodes: MapRc;

% M is the set of nodes in the map pattern.
var set of nodes: M;

% Mc is the complement of M (nodes not in the map pattern).
var set of nodes: Mc;

% MR[i] is the set of nodes of run i in the map.
array[runs] of var set of nodes: MR;

% MRun[j] is the run of node j (or m if j does not belong to M).
array[nodes] of var 0..m: MRun;

% Last run in the map.
var runs: MLast;

% MCount[k] is the number of nodes that correspond to instruction k in a
% map run.
%
% These variables and the corresponding constraints enforce, by construction,
% that all runs contain the same number of nodes and cover the same
% instructions the same number of times. This is an approximation to run
% isomorphism, which is doable but would add a lot of model overhead (the
% isomorphism bijection would have to be modeled explicitly, as there are no
% global constraints available).
array[insts] of var 0..n: MCount;

% R is the set of nodes in the reduction pattern.
var set of nodes: R;

% Rc is the complement of R (nodes not in the reduction pattern).
var set of nodes: Rc;

% S[i] is the set of nodes of step i in the reduction.
array[steps] of var set of nodes: RS;

% Step[j] is the step of node j (or m if j does not belong to R).
array[nodes] of var 0..m: RStep;

% Last step in the reduction.
var steps: RLast;

% RCount[k] is the number of nodes that correspond to instruction k in a
% reduction step.
%
% These variables and the corresponding constraints enforce, by construction,
% that all steps contain the same number of nodes and cover the same
% instructions the same number of times. This is an approximation to step
% isomorphism, which is doable but would add a lot of model overhead (the
% isomorphism bijection would have to be modeled explicitly, as there are no
% global constraints available).
array[insts] of var 0..n: RCount;

%%% CONSTRAINTS

% Ensure that the map variables form a map.
constraint map(M, Mc, MR, MRun, MLast, MCount);

% Ensure that the reduction variables form a linear reduction.
constraint linear_reduction(R, Rc, RS, RStep, RLast, RCount);

% Ensure that there are as many map runs as reduction steps.
constraint MLast == RLast;

% Ensure that there is an arc from each map run to its corresponding partial
% reduction step.
constraint
forall (i in 0..MLast)
(exists (a in index_set_1of2(arcs))
 (
  let {int: s = arcs[a, 0];
       int: t = arcs[a, 1]} in
  ((s in MR[i]) /\ (t in RS[i]))
 )
);

% Ensure that map runs and reduction steps use different instructions.
constraint
forall (k in insts)
(
 (MCount[k] > 0 -> RCount[k] == 0) /\
 (RCount[k] > 0 -> MCount[k] == 0)
);

constraint static_covering(M);

constraint static_covering(R);

constraint minimum_components(MR, 2);

constraint minimum_components(RS, 2);

%%% SOLVER SPECIFICATION

solve satisfy;

output
 ["linear_map_reduction: map:       "] ++
 [show(MR[i]) ++ " " | i in runs ] ++ ["\n"] ++
 ["linear_map_reduction: reduction: "] ++ [ show(RS[i]) ++ " " | i in steps ];
