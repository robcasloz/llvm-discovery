% MiniZinc model for finding tiled reductions.

include "partition_set.mzn";
include "disjoint.mzn";

include "common.mzn";

%%% AUXILIARY DEFINITIONS

% Upper bound on number of partial reductions.
int: m = n div 2;

% Set of potential final reduction steps.
set of int: final_steps = 0..m-1;

% Potential steps of each partial reduction.
set of int: partial_steps = 0..m-1;

%%% VARIABLES

% R is the set of nodes in the entire tiled reduction.
var set of nodes: R;

% Rc is the complement of R (nodes not in the entire tiled reduction).
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

% Count[k] is the number of nodes that correspond to instruction k in a
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

% Count[k] is the number of nodes that correspond to instruction k in a
% partial step (same across all partial reductions).
array[insts] of var 0..n: PCount;

%%% CONSTRAINTS

% Ensure that the partial and final reduction variables form a tiled reduction.
constraint tiled_reduction(R, Rc,
                             PR, PRc, PS, PStep, PLast, PCount,
                             FR, FRc, FS, FStep, FLast, FCount);

% Ensure that the final reduction has at least two steps.
constraint minimum_components(FS, 2);

% Ensure that at least one of the partial reductions has two steps.
constraint
match_trivial \/
(
 exists (i in 0..FLast) (minimum_components(row(PS, i), 2))
);

%%% SOLVER SPECIFICATION

solve satisfy;

output
["tiled_reduction: final:   " ++ show(FS[i]) ++ "\n" ++
 "tiled_reduction: partial: " ++
 concat([show(PS[i,j]) ++ " " | j in partial_steps]) ++ "\n"
 | i in final_steps ]
