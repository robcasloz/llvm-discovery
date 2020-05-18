% MiniZinc model for finding tiled map-reductions.

include "partition_set.mzn";
include "disjoint.mzn";

include "common.mzn";

%%% AUXILIARY DEFINITIONS

% Upper bound on number of map runs and partial reductions.
int: m = n div 3;

% Set of potential map runs.
set of int: runs = 0..m-1;

% Set of potential final reduction steps.
set of int: final_steps = 0..m-1;

% Potential steps of each partial reduction.
set of int: partial_steps = 0..m-1;

%%% VARIABLES

% MapR is the set of nodes in the tiled map-reduction.
var set of nodes: MapR;

% MapRc is the complement of MapR (nodes not in tiled map-reduction).
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

% R is the set of nodes in the tiled reduction.
var set of nodes: R;

% Rc is the complement of R (nodes not in the tiled reduction).
var set of nodes: Rc;

% FR is the set of nodes in the final reduction.
var set of nodes: FR;

% FRc is the complement of FR (nodes not in the final reduction).
var set of nodes: FRc;

% FS[i] is the set of nodes of final step i.
array[final_steps] of var set of nodes: FS;

% FStep[j] is the final step of node j (or m if j is not in the final step).
array[nodes] of var 0..m: FStep;

% Last final step.
var final_steps: FLast;

% FCount[k] is the number of nodes that correspond to instruction k in a
% final step.
array[insts] of var 0..n: FCount;

% PR[i] is the set of nodes in partial reduction i.
array[final_steps] of var set of nodes: PR;

% PRc[i] is the complement of PR[i] (nodes not in partial reduction i).
array[final_steps] of var set of nodes: PRc;

% PS[i][j] is the set of nodes of step j in partial reduction i.
array[final_steps, partial_steps] of var set of nodes: PS;

% PStep[i][j] is the step of node j in partial reduction i (or m if j is not in
% the partial step).
array[final_steps, nodes] of var 0..m: PStep;

% PLast[i] is the last step in partial reduction i (or -1 if the partial
% reduction is empty).
array[final_steps] of var ({-1} union final_steps): PLast;

% PCount[k] is the number of nodes that correspond to instruction k in a
% partial step (same across all partial reductions).
array[insts] of var 0..n: PCount;

% RCount[k] is the number of nodes that correspond to instruction k in any
% reduction step.
array[insts] of var 0..n: RCount;

% PSteps is the number of steps in each non-empty partial reduction.
var partial_steps: PSteps;

%%% CONSTRAINTS

% Ensure that MapR and MapRc are complementary.
constraint
partition_set([MapR, MapRc], nodes);

% Ensure that all map runs and reduction steps form a partition of MapR.
constraint
partition_set([M, R, MapRc], nodes);

% Ensure that the map variables form a map.
constraint map(M, Mc, MR, MRun, MLast, MCount);

% Ensure that the partial and final reduction variables form a tiled reduction.
constraint tiled_reduction(R, Rc,
                             PR, PRc, PS, PStep, PLast, PCount,
                             FR, FRc, FS, FStep, FLast, FCount);

% Ensure that the final reduction has at least two steps.
constraint minimum_components(FS, 2);

% Ensure that at least one of the partial reductions has two steps.
constraint
exists (i in 0..FLast)
(minimum_components(row(PS, i), 2));

% Count the number of times each instruction is used in a reduction step-
constraint
forall (k in insts)
(RCount[k] == PCount[k] + FCount[k]);

% Ensure that map runs and reduction steps use different instructions.
constraint
forall (k in insts)
(
 (MCount[k] > 0 -> RCount[k] == 0) /\
 (RCount[k] > 0 -> MCount[k] == 0)
);

% Enforce that all partial reductions have the same number of steps.
constraint
forall (i in 0..FLast)
(PSteps == card(PR[i]));

% Ensure that there are as many map runs as partial reduction steps.
constraint (MLast + 1) == ((FLast + 1) * PSteps);

% Ensure that there is an arc from each map run to its corresponding partial
% reduction step.
constraint
forall (i in 0..FLast, j in 0..PSteps-1)
(exists (a in index_set_1of2(arcs))
 (
  let {int: s = arcs[a, 0];
       int: t = arcs[a, 1]} in
  ((s in MR[i * PSteps + j]) /\ (t in PS[i, j]))
 )
);

constraint static_covering(M);

constraint static_covering(array_union(PR));

%%% SOLVER SPECIFICATION

solve satisfy;

output
 ["tiled_map_reduction: map:     " ++
  concat([show(MR[i]) ++ " " | i in runs]) ++ "\n"] ++
 ["tiled_map_reduction: final:   " ++ show(FS[i]) ++ "\n" ++
 "tiled_map_reduction: partial: " ++
 concat([show(PS[i,j]) ++ " " | j in partial_steps]) ++ "\n"
 | i in final_steps ]
