% MiniZinc model for finding two-phase reductions.

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

% R is the set of nodes in the entire two-phase reduction.
var set of nodes: R;

% Rc is the complement of R (nodes not in the entire two-phase reduction).
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

% PLast[i] is the last step in partial reduction i.
array[final_steps] of var final_steps: PLast;

% Count[k] is the number of nodes that correspond to instruction k in a
% partial step (same across all partial reductions).
array[insts] of var 0..n: PCount;

%%% CONSTRAINTS

% Ensure that the final reduction variables form a reduction.
constraint reduction(FR, FRc, FS, FStep, FLast, FCount);

% Ensure that each set of partial reduction variables forms a reduction.
constraint
forall (i in 0..FLast)
(reduction(PR[i], PRc[i], row(PS, i), row(PStep, i), PLast[i], PCount));

% Ensure that there are as many partial reductions as steps in the final
% reduction.
constraint
forall (i in final_steps)
(card(PR[i]) > 0 <-> i <= FLast);

% Ensure that empty partial reductions have empty reduction steps.
constraint
forall (i in final_steps, j in partial_steps)
(card(PR[i]) == 0 -> card(PS[i,j]) == 0);


% Ensure that R and Rc are complementary.
constraint
partition_set([R, Rc], nodes);

% Ensure that all reduction steps (partial and final) form a partition of R.
constraint
partition_set([FR] ++ PR ++ [Rc], nodes);

% Ensure that there is an arc from the last step of each partial reduction to
% its corresponding step in the final reduction.
constraint
forall (i in 0..FLast)
(exists (a in index_set_1of2(arcs))
 (
  let {int: s = arcs[a, 0];
       int: t = arcs[a, 1]} in
  ((s in PS[i, PLast[i]]) /\ (t in FS[i]))
 )
);

% Ensure that all partial steps have an incoming arc.
constraint
forall (i in final_steps where i <= FLast,
        j in partial_steps where j <= PLast[i])
(exists (a in index_set_1of2(arcs))
 (
  let {int: s = arcs[a, 0];
       int: t = arcs[a, 1]} in
  ((not (s in R)) /\ (t in PS[i,j]))
 )
);

% Ensure that the last final step has an outgoing arc.
constraint
exists (a in index_set_1of2(arcs))
(
 let {int: s = arcs[a, 0];
      int: t = arcs[a, 1]} in
 ((s in FS[FLast]) /\ (not (t in R)))
);

% Ensure that partial and final reduction steps use different instructions.
constraint
forall (k in insts)
(
 (FCount[k] > 0 -> PCount[k] == 0) /\
 (PCount[k] > 0 -> FCount[k] == 0)
);

% Ensure that the final reduction has at least two steps.
constraint minimum_components(FS, 2);

% Ensure that each active partial reduction has at least one step.
constraint
forall (i in 0..FLast)
(minimum_components(row(PS, i), 1));

% Ensure that at least one of the partial reductions has two steps.
constraint
exists (i in 0..FLast)
(minimum_components(row(PS, i), 2));

% Ensure that each step has just one node.
constraint
forall (i in final_steps)
(card(FS[i]) <= 1);
constraint
forall (i in final_steps, j in partial_steps)
(card(PS[i,j]) <= 1);

%%% SOLVER SPECIFICATION

solve satisfy;

output
["twophasereduction: final:   " ++ show(FS[i]) ++ "\n" ++
 "twophasereduction: partial: " ++
 concat([show(PS[i,j]) ++ " " | j in partial_steps]) ++ "\n"
 | i in final_steps ]
