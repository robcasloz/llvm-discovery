% MiniZinc model for finding conditional maps.

include "partition_set.mzn";
include "disjoint.mzn";
include "increasing.mzn";

include "common.mzn";

% FIXME: express in terms of map(), or define common maplike() predicate.

%%% AUXILIARY DEFINITIONS

% Number of non-control nodes. This can be used as an upper bound on the number
% of map runs (setting m = nnc below).
% TODO: a potentially stronger bound would be the maximum number of nodes that
% are not weakly connected.
int: nnc = card({n | i in 0..c-1, n in static_classes[i]
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

% outgoing[i] indicates whether run has an outgoing arc.
array[runs] of var bool: outgoing;

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

% Ensure that M contains only matchable nodes.
constraint M subset matchable;

% Ensure that M and Mc are complementary.
constraint partition_set([M, Mc], nodes);

% Ensure that the map runs form a partition of M.
constraint partition_set(R ++ [Mc], nodes);

% Ensure that the run of a node j is set to i if j in R[i], or to m otherwise.
% FIXME: use one-based numbering from the beginning?
constraint int_set_channel_zero(Run, R ++ [Mc]);

% Ensure that the last run is non-empty and has an empty successor run.
constraint last_non_empty(Last, R);

% Ensure that all runs are independent. This is enforced by ensuring each arc
% in the DDG is either external, incoming, intra-run, or outgoing.
% FIXME: is this subsumed by the reachability constraints?
constraint
forall (a in index_set_1of2(arcs))
(
 let {int: s = arcs[a, 0];
      int: t = arcs[a, 1]} in
 xorall([
         % external arc
         (not (s in M)) /\ (not (t in M)),
         % incoming arc
         (not (s in M)) /\ (t in M),
         % intra-run arc
         (s in M) /\ Run[t] == Run[s],
         % outgoing arc
         (s in M) /\ (not (t in M))
         ])
);

% Ensure that all runs have an incoming arc.
constraint
forall (i in runs where i <= Last)
(exists (a in index_set_1of2(arcs))
 (
  let {int: s = arcs[a, 0];
       int: t = arcs[a, 1]} in
  ((not (s in M)) /\ (t in R[i]))
 )
);

% Ensure that runs marked as outgoing have outgoing arcs and vice versa.
constraint
forall (i in runs)
(outgoing[i] <->
 (exists (a in index_set_1of2(arcs))
  (
   let {int: s = arcs[a, 0];
        int: t = arcs[a, 1]} in
   ((s in R[i]) /\ (not (t in M)))
  )
 )
);

% Ensure that there exists at least one outgoing run.
constraint exists (i in runs) (outgoing[i]);

% Ensure that there exists at least one non-empty, non-outgoing run.
constraint exists (i in runs where i <= Last) (not outgoing[i]);

% Ensure that there are no holes in the map. A hole is a node that is
% reachable and reaches two map nodes but is not part of the map.
constraint
forall (s in nodes, t in nodes where card(between(s, t)) > 0)
(((s in M) /\ (t in M)) -> between(s, t) subset M);

% Ensure that the nodes of different runs cannot reach each other.
constraint
forall (s in nodes, t in nodes where t in reachable[s])
(((s in M) /\ (t in M)) -> Run[t] == Run[s]);

% Ensure that pairs of nodes that are not "weakly connected" (see definition in
% common.mzn) are assigned different runs. We use "weak connectivity" as a poor
% man's approximation to regular graph connectivity (which would be very costly
% to implement).
constraint
forall (s in nodes, t in nodes where s != t /\ not weakly_connected(s, t))
(((s in M) /\ (t in M)) -> Run[t] != Run[s]);

% Ensure that the map has at least two runs.
constraint minimum_components(R, 2);

% Enforce that no run exceeds the maximum number of nodes of each instruction.
constraint
forall (k in insts)
(Count[k] <= max_count[k]);

% Enforce that all runs contain the same number of nodes and cover the same
% instructions the same number of times.
constraint
forall (i in runs where card(R[i]) > 0, k in insts)
(Count[k] =
 sum(j in nodes where j in static_classes[k])
 (bool2int(j in R[i])));

% Enforce that all runs cover at least one non-control instruction.
constraint exists (k in insts diff branches) (Count[k] > 0);

% Enforce static covering: either all instances of an instruction are covered by
% M or none is.
constraint static_covering(M);

% Enforce run ordering by minimum node, for symmetry breaking.
constraint
increasing([if card(R[i]) > 0 then min(R[i]) else n + 1 endif | i in runs]);

%%% SOLVER SPECIFICATION

solve satisfy;

output ["conditional_map: "] ++ [ show(R[i]) ++ " " | i in runs ];
