% MiniZinc model for finding reductions. Work in progress.
% Run like this:
% $ minizinc -a reduction.mzn map-reduction.dzn

include "partition_set.mzn";
include "disjoint.mzn";

include "common.mzn";

%%% AUXILIARY DEFINITIONS

% Upper bound on number of reduction steps.
int: m = n;

% Set of potential reduction steps.
set of int: steps = 0..m-1;

%%% VARIABLES

% R is the set of nodes in the reduction pattern.
var set of nodes: R;

% Rc is the complement of R (nodes not in the reduction pattern).
var set of nodes: Rc;

% S[i] is the set of nodes of step i in the reduction.
array[steps] of var set of nodes: S;

% Step[j] is the step of node j (or m if j does not belong to R).
array[nodes] of var 0..m: Step;

% Last step in the reduction.
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

% Ensure that R contains only matchable nodes.
constraint R subset matchable;

% Ensure that R and Rc are complementary.
constraint partition_set([R, Rc], nodes);

% Ensure that the reduction steps form a partition of R.
constraint partition_set(S ++ [Rc], nodes);

% Ensure that the step of a node j is set to i if j in S[i], or to m otherwise.
% FIXME: use one-based numbering from the beginning?
constraint int_set_channel_zero(Step, S ++ [Rc]);

% Ensure that the last step is non-empty and has an empty successor step.
constraint last_non_empty(Last, S);

% Ensure that all steps form a chain. This is enforced by 1) ensuring each arc
% in the DDG is either external, incoming, intra-step, inter-step, or outgoing;
constraint
forall (a in index_set_1of2(arcs))
(
 let {int: s = arcs[a, 0];
      int: t = arcs[a, 1]} in
 xorall([
         % external arc
         (not (s in R)) /\ (not (t in R)),
         % incoming arc
         (not (s in R)) /\ (t in R),
         % intra-step arc
         (s in R) /\ Step[t] == Step[s],
         % inter-step arc
         (s in R) /\ Step[t] == Step[s] + 1,
         % outgoing arc, only allowed in the last step
         (s in R) /\ (not (t in R)) /\ Step[s] == Last
         ])
);

% and 2) ensuring that each step has an outgoing arc to the next step.
constraint
forall (i1 in steps, i2 in steps where i2 <= Last /\ i2 = i1 + 1)
(exists (a in index_set_1of2(arcs))
 (
  let {int: s = arcs[a, 0];
       int: t = arcs[a, 1]} in
  ((s in S[i1]) /\ (t in S[i2]))
 )
);

% Ensure that all steps have an incoming arc.
constraint
forall (i in steps where i <= Last)
(exists (a in index_set_1of2(arcs))
 (
  let {int: s = arcs[a, 0];
       int: t = arcs[a, 1]} in
  ((not (s in R)) /\ (t in S[i]))
 )
);

% Ensure that the last step has an outgoing arc.
constraint
exists (a in index_set_1of2(arcs))
(
 let {int: s = arcs[a, 0];
      int: t = arcs[a, 1]} in
 ((s in S[Last]) /\ (not (t in R)))
);

% Ensure that there are no holes in the reduction. A hole is a node that is
% reachable and reaches two reduction nodes but is not part of the reduction.
constraint
forall (s in nodes, t in nodes where card(between(s, t)) > 0)
(((s in R) /\ (t in R)) -> between(s, t) subset R);

% Ensure that the reduction nodes are ordered according to reachability, that
% is, a reduction node in a certain step cannot reach another reduction node in
% an earlier step.
% NOTE: this constraint is logically redundant but strengthens propagation.
constraint
forall (s in nodes, t in nodes where t in reachable[s])
(((s in R) /\ (t in R)) -> Step[t] >= Step[s]);

% Ensure that the reduction has at least two steps.
constraint assert(n > 1, "The DDG should contain at least two nodes");
constraint card(S[0]) > 0;
constraint card(S[1]) > 0;

% Enforce that no step exceeds the maximum number of nodes of each instruction.
constraint
forall (k in insts)
(Count[k] <= max_count[k]);

% Enforce that all steps contain the same number of nodes and cover the same
% instructions the same number of times.
constraint
forall (i in steps where card(S[i]) > 0, k in insts)
(Count[k] =
 sum(j in nodes where j in static_classes[k])
 (bool2int(j in S[i])));

% Enforce static covering: either all instances of an instruction are covered by
% R or none is.
constraint
forall (sc in static_classes, i, j in sc where j > i)
(i in R <-> j in R);

%%% SOLVER SPECIFICATION

solve satisfy;

output ["reduction: "] ++ [ show(S[i]) ++ " " | i in steps ];
