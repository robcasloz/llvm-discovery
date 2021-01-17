% MiniZinc model for finding conditional linear scans.

include "partition_set.mzn";
include "disjoint.mzn";
include "alldifferent.mzn";

include "common.mzn";

% FIXME: express in terms of common linear_scan(), or define common
% linear_scanlike() predicate.

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

% Sn[i] is the node of step i in the scan (or n if not in the scan).
array[steps] of var 0..2*n: Sn;

% outgoing[i] indicates whether step has an outgoing arc.
array[steps] of var bool: outgoing;

% Step[j] is the step of node j (or m if j does not belong to SC).
array[nodes] of var 0..m: Step;

% Last step in the scan.
var steps: Last;

% Only instruction in each step.
var insts: Inst;

%%% CONSTRAINTS

% Ensure that SC contains only matchable nodes.
constraint SC subset matchable;

% Ensure that SC and SCc are complementary.
constraint partition_set([SC, SCc], nodes);

% Ensure that the last step is non-empty and has an empty successor step.
constraint
forall (i in 0..m-2)
(((Sn[i] < n) /\ (Sn[i + 1] >= n)) <-> Last == i);
constraint Sn[m-1] < n <-> Last == m-1;

constraint
forall (i in steps where i <= Last)
(Sn[i] in SC);

constraint
forall (j in SC)
(exists (i in steps)
(Sn[i] == j));

constraint
forall (i in steps where i > Last)
(Sn[i] == n + i);

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
forall (i1 in steps where i1 + 1 <= Last)
(arc(Sn[i1], Sn[i1 + 1]));

% Ensure that all steps have an incoming arc.
constraint
forall (i in steps where i <= Last)
(exists (a in index_set_1of2(arcs))
 (
  let {int: s = arcs[a, 0];
       int: t = arcs[a, 1]} in
  ((not (s in SC)) /\ (t == Sn[i]))
 )
);

% Ensure that steps marked as outgoing have outgoing arcs and viceversa.
constraint
forall (i in steps where i <= Last)
(outgoing[i] <->
 (exists (a in index_set_1of2(arcs))
  (
   let {int: s = arcs[a, 0];
        int: t = arcs[a, 1]} in
   ((s == Sn[i]) /\ (not (t in SC)))
  )
 )
);

% Ensure that there exist at least two outgoing steps.
constraint (sum (i in steps where i <= Last) (bool2int(outgoing[i]))) >= 2;

% Ensure that there exists at least one non-empty, non-outgoing step.
constraint exists (i in steps where i <= Last) (not outgoing[i]);

% Ensure that the scan has at least two steps.
constraint assert(n > 1, "The DDG should contain at least two nodes");
constraint Sn[0] < n;
constraint Sn[1] < n;

% Enforce that all steps contain one node of the same instruction.
constraint
forall (i in steps where i <= Last, k in insts)
(Inst == k <-> Sn[i] in static_classes[k]);

% Enforce that all steps are associative.
constraint Inst in associative;

constraint
forall (j in static_classes[Inst])
(j in SC);

% Enforce step ordering by minimum node (assumes nodes are numbered
% topologically).
constraint
increasing(Sn);

constraint
alldifferent(Sn);

%%% SOLVER SPECIFICATION

solve satisfy;

output ["conditional_linear_scan: "] ++ [ show(if Sn[i] < n then {Sn[i]} else {} endif) ++ " " | i in steps ];
