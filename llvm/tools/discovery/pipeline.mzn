% MiniZinc model for finding pipelines.

include "partition_set.mzn";
include "disjoint.mzn";

include "common.mzn";

%%% AUXILIARY DEFINITIONS

% Upper bound on number of pipeline stages. Each stage must be run at least
% twice.
int: m = n div 2;

% Upper bound on number of pipeline runs (a run corresponds to a data item
% flowing through all pipeline stages). Each run must go through at least two
% stages.
int: l = n div 2;

% Set of potential pipeline stages.
set of int: stages = 0..m-1;

% Set of potential pipeline runs.
set of int: runs = 0..l-1;

%%% VARIABLES

% P is the set of nodes in the pipeline pattern.
var set of nodes: P;

% Pc is the complement of P (nodes not in the pipeline pattern).
var set of nodes: Pc;

% S[i] is the set of nodes of stage i in the pipeline.
array[stages] of var set of nodes: S;

% Stage[k] is the stage of node k (or m if k does not belong to P).
array[nodes] of var 0..m: Stage;

% Last stage in the pipeline.
var stages: LastStage;

% R[j] is the set of nodes of run j in the pipeline.
array[runs] of var set of nodes: R;

% Run[k] is the run of node k (or l if k does not belong to P).
array[nodes] of var 0..l: Run;

% Last run in the pipeline.
var runs: LastRun;

% Count[i][p] is the number of nodes that correspond to instruction p in a
% step of stage i.
array[stages, insts] of var 0..n: Count;

%%% CONSTRAINTS

% Ensure that P contains only matchable nodes.
constraint P subset matchable;

% Ensure that P and Pc are complementary.
constraint partition_set([P, Pc], nodes);

% Ensure that the pipeline stages form a partition of P.
constraint partition_set(S ++ [Pc], nodes);

% Ensure that the pipeline runs form a partition of P.
constraint partition_set(R ++ [Pc], nodes);

% Ensure that the stage of a node k is set to i if k in S[i], or to m otherwise.
% FIXME: use one-based numbering from the beginning?
constraint int_set_channel_zero(Stage, S ++ [Pc]);

% Ensure that the run of a node k is set to j if k in R[j], or to l otherwise.
% FIXME: use one-based numbering from the beginning?
constraint int_set_channel_zero(Run, R ++ [Pc]);

% Ensure that the last stage is non-empty and has an empty successor stage.
constraint last_non_empty(LastStage, S);

% Ensure that the last run is non-empty and has an empty successor run.
constraint last_non_empty(LastRun, R);

% Ensure that all steps form a pipeline. This is enforced by ensuring each arc
% in the DDG is either external, incoming, intra-step, inter-step (state),
% inter-step (forward) or outgoing.
constraint
forall (a in index_set_1of2(arcs))
(
 let {int: s = arcs[a, 0];
      int: t = arcs[a, 1]} in
 xorall([
         % external arc
         (not (s in P)) /\ (not (t in P)),
         % incoming arc
         (not (s in P)) /\ (t in P),
         % intra-step arc
         (s in P) /\ Stage[t] == Stage[s] /\ Run[t] == Run[s],
         % inter-step, state arc
         (s in P) /\ Stage[t] == Stage[s] /\ Run[t] == Run[s] + 1,
         % inter-step, forward arc
         (s in P) /\ Stage[t] == Stage[s] + 1 /\ Run[t] == Run[s],
         % outgoing arc, only allowed in the last stage
         (s in P) /\ (not (t in P)) /\ Stage[s] == LastStage
         ])
);

% Enforce that, for all but the last stage, there is at least one step that
% reaches the successor stage.
% TODO: enforce for all but the last stage (now enforcing only once).
constraint
exists(a in index_set_1of2(arcs))
(
 let {int: s = arcs[a, 0];
      int: t = arcs[a, 1]} in
 ((s in P) /\ Stage[t] == Stage[s] + 1 /\ Run[t] == Run[s])
);

% Ensure that there are no holes in the pipeline. A hole is a node that is
% reachable and reaches two pipeline nodes but is not part of the pipeline.
constraint
forall (s in nodes, t in nodes where card(between(s, t)) > 0)
(((s in P) /\ (t in P)) -> between(s, t) subset P);

% Ensure that the pipeline nodes are ordered according to reachability, that
% is, a pipeline node in a certain stage cannot reach another pipeline node in
% an earlier stage.
% NOTE: this constraint is logically redundant but strengthens propagation.
constraint
forall (s in nodes, t in nodes where t in reachable[s])
(((s in P) /\ (t in P)) -> Stage[t] >= Stage[s]);

% Ensure that the pipeline has at least two stages and two runs.
constraint minimum_components(S, 2);
constraint minimum_components(R, 2);

% Enforce that no step exceeds the maximum number of nodes of each instruction.
constraint
forall (i in stages, p in insts)
(Count[i, p] <= max_count[p]);

% Enforce that all steps within a stage contain the same number of nodes and
% cover the same static operations the same number of times.
constraint
forall (i in stages, j in runs, p in insts where card(R[j]) > 0)
(Count[i, p] =
 sum(k in nodes where k in static_classes[p])
 (bool2int(k in S[i] /\ k in R[j])));

% Enforce static covering: either all instances of an instruction are covered by
% P or none is.
constraint static_covering(P);

%%% SOLVER SPECIFICATION

solve satisfy;

output ["pipeline: stages: "] ++ [ show(S[i]) ++ " " | i in stages ] ++ ["\n"]
    ++ ["pipeline: runs:   "] ++ [ show(R[j]) ++ " " | j in runs ] ++ ["\n"];
