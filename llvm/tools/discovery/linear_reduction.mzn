% MiniZinc model for finding linear reductions.

include "partition_set.mzn";
include "disjoint.mzn";

include "common.mzn";

%%% AUXILIARY DEFINITIONS

% Upper bound on number of reduction steps.
int: m = n;

% Set of potential reduction steps.
set of int: steps = 0..m-1;

%%% VARIABLES

% R is the set of nodes in the linear reduction pattern.
var set of nodes: R;

% Rc is the complement of R (nodes not in the linear reduction pattern).
var set of nodes: Rc;

% S[i] is the set of nodes of step i in the reduction.
array[steps] of var set of nodes: S;

% Step[j] is the step of node j (or m if j does not belong to R).
array[nodes] of var 0..m: Step;

% Last step in the linear reduction.
var steps: Last;

% Count[k] is the number of nodes that correspond to instruction k in a
% reduction step.
%
% These variables and the corresponding constraints enforce, by construction,
% that all steps contain the same number of nodes and cover the same
% instructions the same number of times. This is an approximation to step
% isomorphism, which is doable but would add a lot of model overhead (the
% isomorphism bijection would have to be modeled explicitly, as there are no
% global constraints available).
array[insts] of var 0..n: Count;

%%% CONSTRAINTS

constraint linear_reduction(R, Rc, S, Step, Last, Count);

constraint static_covering(R);

constraint minimum_components(S, 2);

%%% SOLVER SPECIFICATION

solve satisfy;

output ["linear_reduction: "] ++ [ show(S[i]) ++ " " | i in steps ];
