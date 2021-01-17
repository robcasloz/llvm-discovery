include "int_set_channel.mzn";
include "increasing.mzn";

%%% PARAMETERS

% Number of nodes in the DDG.
int: n;

% Number of instructions.
int: c;

% Number of operations.
int: o;

% Set of matchable nodes.
set of 0..n-1: matchable;

% Arcs in the DDG.
array[int,int] of 0..n-1: arcs;

% Sets of nodes that correspond to the same instruction.
array[0..c-1] of set of 0..n-1: static_classes;

% Sets of nodes that correspond to the same operation.
array[0..o-1] of set of 0..n-1: operation_classes;

% Nodes reachable from each node.
array[0..n-1] of set of 0..n-1: reachable;

% Set of branch instructions.
set of 0..c-1: branches;

% Set of associative instructions.
set of 0..c-1: associative;

% Maximum number of nodes of the same instruction in each pattern component.
array[0..c-1] of 0..n: max_count;

% Whether trivial patterns are matched.
bool: match_trivial;

%%% AUXILIARY DEFINITIONS

% Set of nodes in the DDG.
set of int: nodes = 0..n-1;

% Set of instructions.
set of int: insts = 0..c-1;

% Set of nodes that reach node j.
function set of nodes: reaching(nodes: j) =
{i | i in nodes where j in reachable[i]};

% Whether there is an arc from node s to node p.
function var bool: arc(var nodes: s, var nodes: p) =
exists (a in index_set_1of2(arcs)) (s == arcs[a, 0] /\ p == arcs[a, 1]);

% Set of nodes reachable from p and reaching s.
function set of nodes: between(nodes: p, nodes: s) =
(reachable[p] intersect reaching(s)) diff {p, s};

% Whether i can reach j, there is a non-source node k that can reach both,
% j can reach i, or there is a node k that can be reached by both.
function bool: weakly_connected(nodes: i, nodes: j) =
(j in reachable[i]) \/
(exists (k in nodes where k != 0) (i in reachable[k] /\ j in reachable[k])) \/
(i in reachable[j]) \/
(exists (k in nodes) (k in reachable[i] /\ k in reachable[j]));

% Like 'int_set_channel' but with zero-based indices.
predicate int_set_channel_zero(array [int] of var int: x,
                               array [int] of var set of int: y) =
let {array[index_set(x)] of var int: x_plus_one;} in
  int_set_channel(x_plus_one, y) /\
  (forall (i in index_set(x)) (x[i] == x_plus_one[i] - 1));

% Sets l to the index of the last non-empty set in x.
% TODO: can we use some form of channeling here?
predicate last_non_empty(var int: l, array [int] of var set of int: x) =
let {int: last = max(index_set(x));} in
  (forall (i in 0..(last - 1))
  (((card(x[i]) > 0) /\ (card(x[i + 1]) == 0)) <-> l == i))
  /\
  (card(x[last]) > 0 <-> l == last);

% Ensures that the given variables capture a map pattern.
predicate map(var set of int: M,
              var set of int: Mc,
              array[int] of var set of int: R,
              array[int] of var int: Run,
              var int: Last,
              array[int] of var int: Count) =
let {set of int: runs = index_set(R);} in
(
 % Ensure that M contains only matchable nodes.
 M subset matchable
)
/\
(
 % Ensure that M and Mc are complementary.
 partition_set([M, Mc], nodes)
)
/\
(
 % Ensure that the map runs form a partition of M.
 partition_set(R ++ [Mc], nodes)
)
/\
(
 % Ensure that the run of a node j is set to i if j in R[i], or to m otherwise.
 % FIXME: use one-based numbering from the beginning?
 int_set_channel_zero(Run, R ++ [Mc])
)
/\
(
 % Ensure that the last run is non-empty and has an empty successor run.
 last_non_empty(Last, R)
)
/\
(
 % Ensure that all runs are independent. This is enforced by ensuring each arc in
 % the DDG is either external, incoming, intra-run, or outgoing.
 % FIXME: is this subsumed by the reachability constraints?
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
  )
)
/\
(
 % Ensure that all runs have an incoming arc.
 forall (i in runs where i <= Last)
 (exists (a in index_set_1of2(arcs))
  (
   let {int: s = arcs[a, 0];
        int: t = arcs[a, 1]} in
   ((not (s in M)) /\ (t in R[i]))
  )
 )
)
/\
(
 % Ensure that all runs have an outgoing arc.
 forall (i in runs where i <= Last)
 (exists (a in index_set_1of2(arcs))
  (
   let {int: s = arcs[a, 0];
        int: t = arcs[a, 1]} in
   ((s in R[i]) /\ (not (t in M)))
  )
 )
)
/\
(
 % Ensure that there are no holes in the map. A hole is a node that is
 % reachable and reaches two map nodes but is not part of the map.
 forall (s in nodes, t in nodes where card(between(s, t)) > 0)
 (((s in M) /\ (t in M)) -> between(s, t) subset M)
)
/\
(
 % Ensure that the nodes of different runs cannot reach each other.
 forall (s in nodes, t in nodes where t in reachable[s])
 (((s in M) /\ (t in M)) -> Run[t] == Run[s])
)
/\
(
 % Ensure that there is at least one run where all nodes are "weakly connected"
 % (see definition in common.mzn). We use "weak connectivity" as a poor man's
 % approximation to regular graph connectivity (which would be very costly to
 % implement).
 exists (i in runs where card(R[i]) > 0)
 (forall (s in R[i], t in R[i]) (weakly_connected(s, t)))
)
/\
(
 % Enforce that no run exceeds the maximum number of nodes of each instruction.
 forall (k in insts)
 (Count[k] <= max_count[k])
)
/\
(
 % Enforce that all runs contain the same number of nodes and cover the same
 % instructions the same number of times.
 forall (i in runs where card(R[i]) > 0, k in insts)
 (Count[k] =
  sum(j in nodes where j in static_classes[k])
  (bool2int(j in R[i])))
)
/\
(
 % Enforce that all runs cover at least one non-control instruction.
 exists (k in insts diff branches) (Count[k] > 0)
);

% Ensures that the given variables capture a linear reduction pattern.
predicate linear_reduction(var set of int: R,
                           var set of int: Rc,
                           array[int] of var set of int: S,
                           array[int] of var int: Step,
                           var int: Last,
                           array[int] of var int: Count) =
let {set of int: steps = index_set(S);} in
(
 % Ensure that R contains only matchable nodes.
 R subset matchable
)
/\
(
 % Ensure that R and Rc are complementary.
 partition_set([R, Rc], nodes)
)
/\
(
 % Ensure that the reduction steps form a partition of R.
 partition_set(S ++ [Rc], nodes)
)
/\
(
 % Ensure that the step of a node j is set to i if j in S[i], or to m otherwise.
 % FIXME: use one-based numbering from the beginning?
 int_set_channel_zero(Step, S ++ [Rc])
)
/\
(
 % Ensure that the last step is non-empty and has an empty successor step.
 last_non_empty(Last, S)
)
/\
(
 % Ensure that all steps form a chain. This is enforced by 1) ensuring each arc
 % in the DDG is either external, incoming, intra-step, inter-step, or outgoing;
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
  )
)
/\
(
 % and 2) ensuring that each step has an outgoing arc to the next step.
 forall (i1 in steps, i2 in steps where i2 <= Last /\ i2 = i1 + 1)
 (exists (a in index_set_1of2(arcs))
  (
   let {int: s = arcs[a, 0];
        int: t = arcs[a, 1]} in
   ((s in S[i1]) /\ (t in S[i2]))
  )
 )
)
/\
(
 % Ensure that all steps have an incoming arc.
 forall (i in steps where i <= Last)
 (exists (a in index_set_1of2(arcs))
  (
   let {int: s = arcs[a, 0];
        int: t = arcs[a, 1]} in
   ((not (s in R)) /\ (t in S[i]))
  )
 )
)
/\
(
 % Ensure that the last step (if any) has an outgoing arc.
 exists (a in index_set_1of2(arcs))
 (
  let {int: s = arcs[a, 0];
       int: t = arcs[a, 1]} in
  (card(R) > 0) -> ((s in S[Last]) /\ (not (t in R)))
 )
)
/\
(
 % Ensure that there are no holes in the reduction. A hole is a node that is
 % reachable and reaches two reduction nodes but is not part of the reduction.
 forall (s in nodes, t in nodes where card(between(s, t)) > 0)
 (((s in R) /\ (t in R)) -> between(s, t) subset R)
)
/\
(
 % Ensure that the reduction nodes are ordered according to reachability, that
 % is, a reduction node in a certain step cannot reach another reduction node in
 % an earlier step.
 % NOTE: this constraint is logically redundant but strengthens propagation.
 forall (s in nodes, t in nodes where t in reachable[s])
 (((s in R) /\ (t in R)) -> Step[t] >= Step[s])
)
/\
(
 % Enforce that no step exceeds the maximum number of nodes of each instruction.
 forall (k in insts)
 (Count[k] <= max_count[k])
)
/\
(
 % Enforce that all steps contain the same number of nodes and cover the same
 % instructions the same number of times.
 forall (i in steps where card(S[i]) > 0, k in insts)
 (Count[k] =
  sum(j in nodes where j in static_classes[k])
  (bool2int(j in S[i])))
)
/\
(
 % Enforce that all steps are associative.
 forall (i in steps where card(S[i]) > 0)
 (associative(S[i]))
);

% Ensures that the given variables capture a tiled reduction pattern.
predicate tiled_reduction(var set of int: R,
                          var set of int: Rc,
                          array[int] of var set of int: PR,
                          array[int] of var set of int: PRc,
                          array[int, int] of var set of int: PS,
                          array[int, int] of var int: PStep,
                          array[int] of var int: PLast,
                          array[int] of var int: PCount,
                          var set of int: FR,
                          var set of int: FRc,
                          array[int] of var set of int: FS,
                          array[int] of var int: FStep,
                          var int: FLast,
                          array[int] of var int: FCount) =
let {set of int: partial_steps = index_set_2of2(PS);
     set of int: final_steps   = index_set(FS);} in
(
 % Ensure that the final reduction variables form a linear reduction.
 linear_reduction(FR, FRc, FS, FStep, FLast, FCount)
)
/\
(
 % Ensure that each set of partial reduction variables forms a linear reduction.
 forall (i in 0..FLast)
 (linear_reduction(PR[i], PRc[i], row(PS, i), row(PStep, i), PLast[i], PCount))
)
/\
(
 % Define FLast as the last final step.
 forall (i in final_steps)
 (card(FS[i]) > 0 <-> i <= FLast)
)
/\
(
 % Ensure that there are no more partial reductions than steps in the final
 % reduction.
 forall (i in final_steps)
 (card(FS[i]) == 0 -> card(PR[i]) == 0)
)
/\
(
 % Ensure that empty partial reductions have empty reduction steps.
 forall (i in final_steps, j in partial_steps)
 (card(PR[i]) == 0 -> card(PS[i,j]) == 0)
)
/\
(
 % Ensure that R and Rc are complementary.
 partition_set([R, Rc], nodes)
)
/\
(
 % Ensure that all reduction steps (partial and final) form a partition of R.
 partition_set([FR] ++ PR ++ [Rc], nodes)
)
/\
(
 % Ensure that there is an arc from the last step of each non-empty partial
 % reduction to its corresponding step in the final reduction.
 forall (i in 0..FLast where card(PR[i]) > 0)
 (exists (a in index_set_1of2(arcs))
  (
   let {int: s = arcs[a, 0];
        int: t = arcs[a, 1]} in
   ((s in PS[i, PLast[i]]) /\ (t in FS[i]))
  )
 )
)
/\
(
 % Ensure that all partial steps have an incoming arc.
 forall (i in final_steps where i <= FLast,
         j in partial_steps where j <= PLast[i])
 (exists (a in index_set_1of2(arcs))
  (
   let {int: s = arcs[a, 0];
        int: t = arcs[a, 1]} in
   ((not (s in R)) /\ (t in PS[i,j]))
  )
 )
)
/\
(
 % Ensure that the last final step has an outgoing arc.
 exists (a in index_set_1of2(arcs))
 (
  let {int: s = arcs[a, 0];
       int: t = arcs[a, 1]} in
  ((s in FS[FLast]) /\ (not (t in R)))
 )
)
/\
(
 % Ensure that partial and final reduction steps use different instructions.
 forall (k in insts)
 (
  (FCount[k] > 0 -> PCount[k] == 0) /\
  (PCount[k] > 0 -> FCount[k] == 0)
 )
)
/\
(
 % Ensure that partial and final reduction steps use the same operation.
 forall (i in 0..o-1, j, k in R)
 (
  j in operation_classes[i] <-> k in operation_classes[i]
 )
);

% Ensures that the given node set is associative.
predicate associative(var set of int: C) =
(
 card(C) == 1
)
/\
(
 forall (i in 0..c-1, n in C where n in static_classes[i])
 (i in associative)
);

% Ensures that either all instances of an instruction are covered by a pattern
% or none is (static covering).
predicate static_covering(var set of int: P) =
forall (sc in static_classes, i, j in sc where j > i)
(i in P <-> j in P);

% Ensures that the pattern has at least minc components.
predicate minimum_components(array[int] of var set of int: S, int: minc) =
(
 assert(n > minc, "The DDG should contain at least " ++ show(minc) ++ " nodes") /\
 forall (i in (0..minc-1)) (card(S[i]) > 0)
);
