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
