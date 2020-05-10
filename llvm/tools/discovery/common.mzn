include "int_set_channel.mzn";

%%% PARAMETERS

% Number of nodes in the DDG.
int: n;

% Number of instructions.
int: c;

% Set of matchable nodes.
set of 0..n-1: matchable;

% Arcs in the DDG.
array[int,int] of 0..n-1: arcs;

% Sets of nodes that correspond to the same instruction.
array[0..c-1] of set of 0..n-1: static_classes;

% Nodes reachable from each node.
array[0..n-1] of set of 0..n-1: reachable;

% Set of branch instructions.
set of 0..c-1: branches;

% Maximum number of nodes of the same instruction in each pattern component.
array[0..c-1] of 0..n: max_count;

%%% AUXILIARY DEFINITIONS

% Set of nodes in the DDG.
set of int: nodes = 0..n-1;

% Set of instructions.
set of int: insts = 0..c-1;

% Set of nodes that reach node j.
function set of nodes: reaching(nodes: j) =
{i | i in nodes where j in reachable[i]};

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

% Ensures that the given variables capture a reduction pattern.
predicate reduction(var set of int: R,
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
