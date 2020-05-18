% MiniZinc model for finding linear scans.

include "partition_set.mzn";
include "disjoint.mzn";

include "common.mzn";

%%% AUXILIARY DEFINITIONS

% Upper bound on number of scan steps.
int: m = n;

% Set of potential scan steps.
set of int: steps = 0..m-1;

%%% VARIABLES

% SC is the set of nodes in the linear scan pattern.
var set of nodes: SC;

% SCc is the complement of SC (nodes not in the scan pattern).
var set of nodes: SCc;

% S[i] is the set of nodes of step i in the scan.
array[steps] of var set of nodes: S;

% Step[j] is the step of node j (or m if j does not belong to SC).
array[nodes] of var 0..m: Step;

% Last step in the scan.
var steps: Last;

% Count[k] is the number of nodes that correspond to instruction k in a
% scan step.
%
% These variables and the corresponding constraints enforce, by construction,
% that all steps contain the same number of nodes and cover the same
% instructions the same number of times. This is an approximation to step
% isomorphism, which is doable but would add a lot of model overhead (the
% isomorphism bijection would have to be modeled explicitly, as there are no
% global constraints available).
array[insts] of var 0..n: Count;

%%% CONSTRAINTS

% Ensure that SC contains only matchable nodes.
constraint SC subset matchable;

% Ensure that SC and SCc are complementary.
constraint partition_set([SC, SCc], nodes);

% Ensure that the scan steps form a partition of SC.
constraint partition_set(S ++ [SCc], nodes);

% Ensure that the step of a node j is set to i if j in S[i], or to m otherwise.
% FIXME: use one-based numbering from the beginning?
constraint int_set_channel_zero(Step, S ++ [SCc]);

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
         (not (s in SC)) /\ (not (t in SC)),
         % incoming arc
         (not (s in SC)) /\ (t in SC),
         % intra-step arc
         (s in SC) /\ Step[t] == Step[s],
         % inter-step arc
         (s in SC) /\ Step[t] == Step[s] + 1,
         % outgoing arc
         (s in SC) /\ (not (t in SC))
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
  ((not (s in SC)) /\ (t in S[i]))
 )
);

% Ensure that all steps have an outgoing arc. This is what differentiates a scan
% from a reduction pattern.
constraint
forall (i in steps where i <= Last)
(exists (a in index_set_1of2(arcs))
 (
  let {int: s = arcs[a, 0];
       int: t = arcs[a, 1]} in
  ((s in S[i]) /\ (not (t in SC)))
 )
);

% Ensure that there are no holes in the scan. A hole is a node that is
% reachable and reaches two scan nodes but is not part of the scan.
constraint
forall (s in nodes, t in nodes where card(between(s, t)) > 0)
(((s in SC) /\ (t in SC)) -> between(s, t) subset SC);

% Ensure that the scan nodes are ordered according to reachability, that
% is, a scan node in a certain step cannot reach another scan node in
% an earlier step.
% NOTE: this constraint is logically redundant but strengthens propagation.
constraint
forall (s in nodes, t in nodes where t in reachable[s])
(((s in SC) /\ (t in SC)) -> Step[t] >= Step[s]);

% Ensure that the scan has at least two steps.
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

% Enforce that all steps are associative.
constraint
forall (i in steps where card(S[i]) > 0)
(associative(S[i]));

% Enforce static covering: either all instances of an instruction are covered by
% SC or none is.
constraint
forall (sc in static_classes, i, j in sc where j > i)
(i in SC <-> j in SC);

%%% SOLVER SPECIFICATION

solve satisfy;

output ["linear_scan: "] ++ [ show(S[i]) ++ " " | i in steps ];
