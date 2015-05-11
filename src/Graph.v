(******************************************************************************)
(* Copyright (c) 2015 Daniel Lustig, Princeton University                     *)
(*                                                                            *)
(* Permission is hereby granted, free of charge, to any person obtaining a    *)
(* copy of this software and associated documentation files (the "Software"), *)
(* to deal in the Software without restriction, including without limitation  *)
(* the rights to use, copy, modify, merge, publish, distribute, sublicense,   *)
(* and/or sell copies of the Software, and to permit persons to whom the      *)
(* Software is furnished to do so, subject to the following conditions:       *)
(*                                                                            *)
(* The above copyright notice and this permission notice shall be included in *)
(* all copies or substantial portions of the Software.                        *)
(*                                                                            *)
(* THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR *)
(* IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,   *)
(* FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL    *)
(* THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER *)
(* LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING    *)
(* FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER        *)
(* DEALINGS IN THE SOFTWARE.                                                  *)
(******************************************************************************)

Require Import List.
Require Import Arith.
Require Import String.
Require Import Debug.
Require Import Util.
Require Import StringUtil.
Require Import Instruction.

Import ListNotations.
Open Scope list_scope.

(** ** Basic Type Definitions *)

(** *** [Location] *)
(** A [Location] is an (x,y) coordinate representing a particular location
within a microarchitecture.  x represents the pipeline number, and y represents
the pipeline stage (or equivalent) within that pipeline. *)
Definition Location := (nat * nat) % type.

(** *** [GraphNode] and [GraphEdge] *)
(** A [GraphNode] represents a [Microop] at a particular [Location] in the
microarchitecture. *)
Definition GraphNode := (Microop * Location) % type.
(** A [GraphEdge] is a directed edge between two [GraphNode]s. *)
Definition GraphEdge := (GraphNode * GraphNode * string) % type.

(** *** [beq_node] *)
(** Boolean comparison of [GraphNode]s. *)
Definition beq_node
  (a b : GraphNode)
  : bool :=
  match (a, b) with
  | ((i0, (p0, l0)), (i1, (p1, l1))) =>
      andb
      (beq_uop i0 i1)
      (andb (beq_nat p0 p1) (beq_nat l0 l1))
  end.

(** *** [beq_edge] *)
(** Boolean comparison of [GraphEdge]s.  Labels not compared. *)
Definition beq_edge
  (a b : GraphEdge)
  : bool :=
  match (a, b) with
  | ((a1, a2, alabel), (b1, b2, blabel)) =>
      andb (beq_node a1 b1) (beq_node a2 b2)
  end.

Definition GraphvizStringOfAddress
  (a : Address)
  : string :=
  match a with
  | 0 => "x"
  | 1 => "y"
  | 2 => "z"
  | 3 => "w"
  | _ => stringOfNat a
  end.

Definition GraphvizStringOfMemoryAccess
  (divider : string)
  (a : MemoryAccess)
  : string :=
  match a with
  | Read a d => StringOf ["R"; GraphvizStringOfAddress a; divider; stringOfNat d]
  | Write a d => StringOf ["W"; GraphvizStringOfAddress a; divider; stringOfNat d]
  | Fence n => n
  end.

Definition GraphvizShortStringOfGraphNode
  (n : GraphNode)
  : string :=
  match n with
  | (mkMicroop g t n a, (p, l)) =>
      StringOf [
          "n";
          stringOfNat g;
          "_";
          stringOfNat t;
          "_";
          stringOfNat n;
          "_";
          GraphvizStringOfMemoryAccess "_" a;
          "_at_";
          stringOfNat p;
          "_";
          stringOfNat l
      ]
  end.

Definition StringOfGraphEdge
  (e : GraphEdge)
  : string :=
  match e with
  | (s, d, label) =>
    StringOf [
      tab; GraphvizShortStringOfGraphNode s; " -> ";
      GraphvizShortStringOfGraphNode d; " [label="; quote; label; quote; "]";
      newline]
  end.

Fixpoint DumpGraphHelper
  (l l' : list GraphEdge)
  : list GraphEdge :=
  match l with
  | h::t =>
      DumpGraphHelper t (Printf h (StringOfGraphEdge h) :: l')
  | [] => rev' l'
  end.

Definition DumpGraph
  (l : list GraphEdge)
  : list GraphEdge :=
  DumpGraphHelper l [].

(** ** Helper Functions *)

(** *** [ReverseEdge] *)
(** Return the edge pointing the opposite direction *)
Definition ReverseEdge
  (e : GraphEdge)
  : GraphEdge :=
  match e with
  | (s, d, l) =>
      (d, s, l)
  end.

(** * Topological Sort *)

(** ** [AdjacencyList] *)
Definition AdjacencyList := list (GraphNode * list (GraphNode * string)).

(** ** [AdjacencyList] Operations *)

(** *** [AdjacencyListAddEdgeHelper] *)
(** Given an adjacency list [l_new], add the edge [(s, d, label)] *)
Fixpoint AdjacencyListAddEdgeHelper
  (s d : GraphNode)
  (label : string)
  (l_old l_new : AdjacencyList)
  : bool * AdjacencyList :=
  match l_new with
  | (h_s, h_ds)::t =>
      if beq_node s h_s
      then (true, app_rev l_old ((h_s, (d, label) :: h_ds) :: t))
      else AdjacencyListAddEdgeHelper s d label ((h_s, h_ds) :: l_old) t
  | [] => (true, (s, [(d, label)]) :: l_old)
  end.

(** *** [AdjacencyListAddEdge] *)
(** Add a [GraphEdge] to an [AdjacencyList], and report whether the edge was
new *)
Definition AdjacencyListAddEdge
  (l : AdjacencyList)
  (e : GraphEdge)
  : bool * AdjacencyList :=
  match e with
  | (s, d, label) =>
      AdjacencyListAddEdgeHelper s d label [] l
  end.

(** Add a [GraphEdge] to an [AdjacencyList], and don't report if the edge was
new *)
Definition AdjacencyListAddEdge2
  (l : AdjacencyList)
  (e : GraphEdge)
  : AdjacencyList :=
  match AdjacencyListAddEdge l e with
  | (_, l') => l'
  end.

(** *** [AdjacencyListFromEdges] *)
(** Create an [AdjacencyList] from a list of [GraphEdge]s *)
Fixpoint AdjacencyListFromEdges
  (l : list GraphEdge)
  : AdjacencyList :=
  fold_left AdjacencyListAddEdge2 l [].

(** ** [NodesFromEdges] *)
(** Given a list of [GraphEdge]s, return the list of [GraphNode]s used in the
edges, without duplicates. *)
Fixpoint NodesFromEdgesHelper
  (l : list GraphEdge)
  (r : list GraphNode)
  : list GraphNode :=
  match l with
  | (h1, h2, label)::t =>
      let r1 :=
        match find (beq_node h1) r with
        | Some _ => r
        | None => h1 :: r
        end in
      let r2 :=
        match find (beq_node h2) r1 with
        | Some _ => r1
        | None => h2 :: r1
        end in
      NodesFromEdgesHelper t r2
  | [] => r
  end.

Definition NodesFromEdges
  (l : list GraphEdge)
  : list GraphNode :=
  NodesFromEdgesHelper l [].

(** *** [EdgesFromAdjacencyList] *)
(** Return the list of [GraphEdge]s in an [AdjacencyList] *)
Fixpoint EdgesFromAdjacencyList
  (l : AdjacencyList)
  : list GraphEdge :=
  let f x :=
    let g y :=
      match y with
      | (d, label) => (fst x, d, label)
      end in
    map g (snd x) in
  let l' := map f l in
  fold_left (app_tail (A:=_)) l' [].

(** *** [NodesFromAdjacencyList] *)
(** Return the set of [GraphNode]s used in an [AdjacencyList] *)
Definition NodesFromAdjacencyList
  (l : AdjacencyList)
  : list GraphNode :=
  NodesFromEdges (EdgesFromAdjacencyList l).

(** *** [AdjacencyListFind] *)
(** Return the label of the edge [(s, d)] if it is contained in the
[AdjacencyList], and [None] otherwise. *)
Fixpoint AdjacencyListFind
  (l : AdjacencyList)
  (s d : GraphNode)
  : option string :=
  match find (fun x => beq_node s (fst x)) l with
  | Some l' =>
      match find (fun x => beq_node (fst x) d) (snd l') with
      | Some (d, label) => Some label
      | None => None
      end
  | None => None
  end. 

(** *** [AdjacencyListGetDsts] *)
(** Return the set of [GraphNode]s reachable from the given source node, or the
empty list if not found. *)
Fixpoint AdjacencyListGetDsts
  (l : AdjacencyList)
  (s : GraphNode)
  : list (GraphNode * string) :=
  match find (fun x => beq_node s (fst x)) l with
  | Some l' => snd l'
  | None => []
  end. 

(** *** [AdjacencyListRemove] *)
(** Remove the node [(s, d)] from an [AdjacencyList] *)
Fixpoint AdjacencyListRemoveHelper
  (s : GraphNode)
  (ds : list (GraphNode * string))
  (d : GraphNode)
  : GraphNode * list (GraphNode * string) :=
  (s, removeb (fun x => beq_node d (fst x)) ds).

Fixpoint AdjacencyListRemove
  (l : AdjacencyList)
  (s d : GraphNode)
  : AdjacencyList :=
  match l with
  | (h1, h2)::t =>
      if beq_node s h1
      then AdjacencyListRemoveHelper h1 h2 d :: t
      else (h1, h2) :: AdjacencyListRemove t s d
  | [] => []
  end.

(** *** [AdjacencyListRemoveSource] *)
(** Remove all edges originating from [s] in the [AdjacencyList] *)
Fixpoint AdjacencyListRemoveSource
  (l : AdjacencyList)
  (s : GraphNode)
  : AdjacencyList :=
  match l with
  | (h1, h2)::t =>
      if beq_node s h1
      then t
      else (h1, h2) :: AdjacencyListRemoveSource t s
  | [] => []
  end.

(** *** [AdjacencyListFilter] *)
(** Remove all edges in the [AdjacencyList] for which
[f (s, d, label) = false], and return the resulting list of edges. *)
Fixpoint AdjacencyListFilterHelper
  (f : GraphEdge -> bool)
  (s : GraphNode)
  (d : list (GraphNode * string))
  : list GraphEdge :=
  match d with
  | (h, label)::t =>
      if f (s, h, label)
      then (s, h, label) :: AdjacencyListFilterHelper f s t
      else                  AdjacencyListFilterHelper f s t
  | [] => []
  end.

Fixpoint AdjacencyListFilter
  (f : GraphEdge -> bool)
  (l : AdjacencyList)
  : list GraphEdge :=
  match l with
  | (hs, hd)::t =>
      AdjacencyListFilterHelper f hs hd ++ AdjacencyListFilter f t
  | [] => []
  end.

(** ** Topological Sort *)

(**
<<
Pseudocode from Wikipedia, attributed to Kahn 1962.

     L = Empty list that will contain the sorted elements
     S = Set of all nodes with no incoming edges
 1   while S is non-empty do
 1       remove a node n from S
 1       add n to tail of L
   2     for each node m with an edge e from n to m do
   2         remove edge e from the graph
   2         if m has no other incoming edges then
   2             insert m into S
 1   if graph has edges then
 1       return error (graph has at least one cycle)
 1   else 
 1       return L (a topologically sorted order)

 1: [TopsortHelper]
 2: [TopsortHelperProcessNode]
>>
*)

(** a Topological Sort can return three types of [TopsortResult]: a total
order (returned here in reverse order, for the convenience of the
[TransitiveClosure] algorithm), a cycle (in which case no topological sort is
possible), or an error. *)
Inductive TopsortResult : Set :=
| ReverseTotalOrder : list GraphNode -> TopsortResult
| Cyclic : list GraphEdge -> TopsortResult
| Abort : nat -> TopsortResult.

(** *** [SourceNodes] *)
(** Return the list of [GraphNode]s from [srcs] which have no incoming edges
listed in [l]. *)
Fixpoint SourceNodes
  (l : list GraphEdge)
  (srcs : list GraphNode)
  : list GraphNode :=
  match l with
  | (h1, h2, label)::t => SourceNodes t (removeb (beq_node h2) srcs)
  | [] => srcs
  end.

(** *** [TopsortHelperProcessNode] *)
(** For each node m with an edge ([n], m), remove ([n], m) from the list of
edges, and then if m is left with no more incoming edges, add it to [s]. *)
Fixpoint TopsortHelperProcessNode
  (l : list GraphNode)
  (s : list GraphNode)
  (n : GraphNode)
  (incoming : AdjacencyList)
  : AdjacencyList * list GraphNode :=
  match l with
  | h::t => 
      (* Remove edge (h, n) *)
      let incoming' := AdjacencyListRemove incoming h n in
      match AdjacencyListGetDsts incoming' h with
      | [] => (* n has no more incoming edges *)
          TopsortHelperProcessNode t (h :: s) n incoming'
      | _  => (* n still has more incoming edges *)
          TopsortHelperProcessNode t       s  n incoming'
      end
  | [] => (incoming, s)
  end.

(** *** [TopsortHelper] *)
(** Perform the outer loop of the topological sort algorithm *)
Fixpoint TopsortHelper
  (i : nat) (* Termination criterion *)
  (l s : list GraphNode)
  (outgoing incoming : AdjacencyList)
  : TopsortResult :=
  match (i, s) with
  | (S i', h::t) =>
      (* Process the node [h] at the head of [s] *)
      let dsts := map (fst (A:=_) (B:=_)) (AdjacencyListGetDsts outgoing h) in
      let (incoming', s') :=
        TopsortHelperProcessNode dsts t h incoming in
      (* Remove [h] from the [AdjacencyList] *)
      let outgoing' := AdjacencyListRemoveSource outgoing h in
      (* Add [h] to the front of [l] (which is in reverse order *)
      let l' := h :: l in
      (* Recurse *)
      TopsortHelper i' l' s' outgoing' incoming'
  | (S i', []) =>
      match EdgesFromAdjacencyList outgoing with
      | [] => (* No more edges in the graph - no cycle, total order found *)
          ReverseTotalOrder l
      | remaining_edges => (* Edges still remain in the graph - cycle found *)
          Cyclic remaining_edges
      end
  | (O, _) => (* Unexpected early termination! *) Abort 0
  end.

(** *** [AdjacencyListTopsort] *)
(** Calculate the topological sort of an [AdjacencyList] *)
Definition AdjacencyListTopsort
  (a : AdjacencyList)
  : TopsortResult :=
  let e := EdgesFromAdjacencyList a in
  let n := NodesFromAdjacencyList a in
  let i := List.length n + List.length e in
  let s := SourceNodes e (map (fst (A:=_) (B:=_)) a) in
  let a' := AdjacencyListFromEdges (map ReverseEdge e) in
  TopsortHelper i [] s a a'.

(** *** [Topsort] *)
(** Calculate the topological sort of a list of [GraphEdge]s. *)
Definition Topsort
  (e : list GraphEdge)
  : TopsortResult :=
  let a := AdjacencyListFromEdges e in
  let n := NodesFromAdjacencyList a in
  let i := List.length n + List.length e in
  let s := SourceNodes e (map (fst (A:=_) (B:=_)) a) in
  let a' := AdjacencyListFromEdges (map ReverseEdge e) in
  TopsortHelper i [] s a a'.

(** ** Transitive Closure *)

Open Scope string_scope.

(** *** [TransitiveClosureHelper2] *)
(** Given a list [preds] of nodes [m] such that [(m, n)] is an edge in the
graph, add [succs] to the list of nodes reachable from [m], where [succs] is
the list of nodes reachable from [n]. *)
Fixpoint TransitiveClosureHelper2
  (a' tc : AdjacencyList)
  (preds : list (GraphNode * string))
  (succs : list GraphNode)
  : AdjacencyList :=
  match preds with
  | (h, _)::t =>
      let getLabel x :=
        match AdjacencyListFind a' x h with
        | Some label => label
        | None => "TC"
        end in
      let f x := (h, x, getLabel x) in
      let edges := map f succs in
      let tc' := fold_left AdjacencyListAddEdge2 edges tc in
      TransitiveClosureHelper2 a' tc' t succs
  | [] => tc
  end.

(** *** [TransitiveClosureHelper] *)
(** Add the list of nodes reachable from [n] to the list of nodes reachable
from each node with an edge going to [n] *)
Definition TransitiveClosureHelper
  (a' tc : AdjacencyList)
  (n : GraphNode)
  : AdjacencyList :=
  let preds := AdjacencyListGetDsts a' n in
  let succs := Map (fst (A:=_) (B:=_)) (AdjacencyListGetDsts tc n) in
  TransitiveClosureHelper2 a' tc preds (n :: succs).

(** *** [TransitiveClosureResult] *)
(** Make it explicit when the algorithm failed. *)
Inductive TransitiveClosureResult : Set :=
| TC : AdjacencyList -> TransitiveClosureResult
| TCError : list GraphEdge -> TransitiveClosureResult.

(** *** [TransitiveClosure] *)
(** Calculate the transitive closure of a list of [GraphEdge]s. *)
Definition TransitiveClosure
  (l : list GraphEdge)
  : TransitiveClosureResult :=
  (* Inverse-adjacency list: the list of nodes [m] which have an edge going to
     [n].  Used to determine the predecessors of a node [n] *)
  let a' := AdjacencyListFromEdges (map ReverseEdge l) in
  (* First do a [Topsort], then use that result to calculate the transitive
     closure *)
  match Topsort l with
  | ReverseTotalOrder l' => TC (fold_left (TransitiveClosureHelper a') l' [])
  | Cyclic e => TCError e (* FIXME: transitive closure of a cyclic graph *)
  | Abort _ => TCError [] (* FIXME: transitive closure of a cyclic graph *)
  end.

(** *** [AdjacencyListTransitiveClosure] *)
(** Calculate the transitive closure of an [AdjacencyList]. *)
Fixpoint AdjacencyListTransitiveClosure
  (a : AdjacencyList)
  : TransitiveClosureResult :=
  let e := EdgesFromAdjacencyList a in
  TransitiveClosure e.

(** ** Transitive Reduction *)
(** Drawing every edge in the transitive closure of the graph would be
extremely messy.  Instead, we can easily eliminate redundant edges along a
single "row" or "column" of the graph.*)

Definition IsTC
  (s : string)
  : bool :=
  match s with
  | String "T" (String "C" EmptyString) => true
  | _ => false
  end.

(** We don't actually want to remove *all* of the redundant edges; some of them
are actually better to keep in the graph for a better conceptual understanding.
For example: although (i1, store buffer) -> (i1, memory) -> (i2, store buffer)
may be true, it looks incomplete conceptually to not have the edge
(i1, store buffer) -> (i2, store buffer) in the graph. *)
Fixpoint TransitiveReductionCondition
  (a b c : GraphNode)
  (ab_label bc_label : string)
  (a_dst : GraphNode * string)
  : bool :=
  let ac_label := snd a_dst in
  match (a, b, c) with
  | ((ia, (pa, la)), (ib, (pb, lb)), (ic, (pc, lc))) =>
      fold_left andb [
        beq_string ab_label "propagated";
        beq_string bc_label "propagated";
        beq_string ac_label "propagated"
        ] true
  end.

(** *** [AdjacencyListTransitiveReduction] *)

(** Given [a], [b], and a list of [c] candidates, remove any (a --> c) edges
which (via [b]) are redundant, according to the condition
[TransitiveReductionCondition]. *)
Fixpoint AdjacencyListTransitiveReductionHelper3
  (a b : GraphNode)
  (ab_label : string)
  (b_ds : list (GraphNode * string))
  (a_ds' : list (GraphNode * string)) (* tail recursion result input *)
  : list (GraphNode * string) :=
  match b_ds with
  | (c, bc_label)::t =>
      let a_ds'' :=
        let f x := andb (beq_node (fst x) c)
          (TransitiveReductionCondition a b c ab_label bc_label x) in
        removeb f a_ds' in
      AdjacencyListTransitiveReductionHelper3 a b ab_label t a_ds''
  | [] => a_ds'
  end.

(** Given [a] and a list of [b] candidates, find the list of [c] candidates. *)
Fixpoint AdjacencyListTransitiveReductionHelper2
  (g : AdjacencyList)
  (a : GraphNode)
  (a_ds : list (GraphNode * string))
  (a_ds' : list (GraphNode * string)) (* tail recursion result input *)
  : GraphNode * list (GraphNode * string) :=
  match a_ds with
  | (b, label)::t =>
      (* If a node is reachable from [h] and from [s], there is no need to
         draw the edge from [s], since it is redundant. *)
      let b_ds := AdjacencyListGetDsts g b in
      AdjacencyListTransitiveReductionHelper2 g a t
      (AdjacencyListTransitiveReductionHelper3 a b label b_ds a_ds')
  | [] => (a, a_ds')
  end.

(** Iterate through [g] to find the list of [a], [b] candidate pairs *)
Fixpoint AdjacencyListTransitiveReductionHelper
  (g : AdjacencyList)
  (g' : AdjacencyList) (* tail recursion result input *)
  : AdjacencyList :=
  match g' with
  | (a, ds)::t =>
      AdjacencyListTransitiveReductionHelper2 g a ds ds ::
      AdjacencyListTransitiveReductionHelper g t
  | [] => []
  end.

(** Calculate the transitive reduction of an adjacency list, but only delete
edges which satisfy the condition [TransitiveReductionCondition].  The goal is
to make the graph output cleaner but still informative, rather than to make the
graphs absolutely minimal. *)
Definition AdjacencyListTransitiveReduction
  (g : AdjacencyList)
  : AdjacencyList :=
  let f x := negb (IsTC (snd x)) in
  let g' := AdjacencyListFromEdges (AdjacencyListFilter f g) in
  AdjacencyListTransitiveReductionHelper g' g'.

(** ** Cycle Detection *)

(** One iteration of depth-first search: if the dst at the head of [dsts] is
[target], then we found the cycle: return it.  Otherwise, iterate one level
deeper.  If [dsts] is empty, then no cycle can be found from this point: back
up and try again with a different node. *)
Fixpoint CycleFromNodeHelper
  (g : AdjacencyList)
  (source target : GraphNode)
  (dsts : list (GraphNode * string))
  (l : list GraphEdge) (* tail recursion result input *)
  (i : nat) (* termination condition *)
  : option (list GraphEdge) :=
  match (i, dsts) with
  | (S i', (h, label)::t) =>
      if beq_node h target
      then (* Found the target and hence the cycle *)
        Some ((source, h, label) :: l)
      else (* Recurse one iteration deeper *)
        match CycleFromNodeHelper g h target (AdjacencyListGetDsts g h)
          ((source, h, label) :: l) i' with
        | Some l' => (* Found a cycle deeper; pass it along upwards *)
            Some l'
        | None => (* Didn't find a cycle; try again with the next dst node *)
            CycleFromNodeHelper g source target t l i'
        end
  | (S i', []) => (* Tried all of the dsts, but no cycle found *) None
  | _ => (* Error: reached the artificial termination condition *) None
  end.

(** *** [CycleFromNode] *)
(** Check whether there is a cycle in [l] including node [n].  If so, return
the edges in the cycle.  If not, return [None]. *)
Definition CycleFromNode
  (l : list GraphEdge)
  (n : GraphNode)
  : option (list GraphEdge) :=
  let g := AdjacencyListFromEdges l in 
  CycleFromNodeHelper g n n (AdjacencyListGetDsts g n) [] (List.length l).

(** Check whether there is a cycle from the node at the head of the list. *)
Fixpoint FindCycleHelper
  (l : list GraphEdge)
  (nodes : list GraphNode)
  : option (list GraphEdge) :=
  match nodes with
  | h::t =>
      match CycleFromNode l h with
      | Some l' => Some l'
      | None => FindCycleHelper l t
      end
  | [] => None
  end.

(** *** [FindCycle] *)
(** Find whether there is any cycle in [l].  If so, return the edges forming
the cycle. *)
Fixpoint FindCycle
  (l : list GraphEdge)
  : option (list GraphEdge) :=
  FindCycleHelper l (NodesFromEdges l).

(** ** [AdjacencyList], [Topsort], and [TransitiveClosure] Examples. *)

Module AdjacencyListExample.

Definition i0 := mkMicroop 0 0 0 (Write 0 1).
Definition i1 := mkMicroop 1 1 0 (Read  0 1).
Definition i2 := mkMicroop 2 1 0 (Read  1 0).

Definition g := [
    ((i2, (1, 0)), (i0, (0, 2)), "a");
    ((i0, (0, 2)), (i1, (1, 3)), "b");
    ((i0, (0, 2)), (i1, (1, 4)), "c")
  ].

Definition l := [
    ((i2, (1, 0)), [((i0, (0, 2)), "a")]);
    ((i0, (0, 2)), [((i1, (1, 4)), "c"); ((i1, (1, 3)), "b")])
  ].

Example AdjacencyListExample1 :
  AdjacencyListFromEdges g = l.
Proof.
auto.
Qed.

Example AdjacencyListExample2 :
  AdjacencyListFind l (i2, (1, 0)) (i0, (0, 2)) = Some "a".
Proof.
auto.
Qed.

Example AdjacencyListExample3 :
  AdjacencyListFind l (i2, (1, 0)) (i0, (0, 4)) = None.
Proof.
auto.
Qed.

Definition n := [
    (i1, (1, 4)); (i1, (1, 3)); (i0, (0, 2)); (i2, (1, 0))
  ].

Example AdjacencyListExample4 :
  NodesFromEdges g = n.
Proof.
  cbv.
auto.
Qed.

Example AdjacencyListExample5 :
  TransitiveClosure g = TC [
    ((i2, (1, 0)),
      [((i1, (1, 4)), "TC"); ((i1, (1, 3)), "TC"); ((i0, (0, 2)), "a")]);
    ((i0, (0, 2)),
      [((i1, (1, 3)), "b"); ((i1, (1, 4)), "c")])
  ].
Proof.
auto.
Qed.

Example AdjacencyListExample6 :
  SourceNodes g (NodesFromEdges g) = [(i2, (1, 0))].
Proof.
auto.
Qed.

Example AdjacencyListExample7 :
  Topsort g = ReverseTotalOrder [
    (i1, (1, 4)); (i1, (1, 3)); (i0, (0, 2)); (i2, (1, 0))].
Proof.
auto.
Qed.

Example AdjacencyListExample8 :
  AdjacencyListTransitiveReduction
   [((i0, (0, 0)), [((i0, (0, 1)), "a"); ((i0, (0, 2)), "b")]);
    ((i0, (0, 1)), [((i0, (0, 2)), "c")])] =
   [((i0, (0, 1)), [((i0, (0, 2)), "c")]);
    ((i0, (0, 0)), [((i0, (0, 2)), "b"); ((i0, (0, 1)), "a")])].
Proof.
auto.
Qed.

Example AdjacencyListExample9 :
  CycleFromNode
    [((i0, (0, 0)), (i0, (0, 1)), "a");
     ((i0, (0, 1)), (i0, (0, 2)), "b");
     ((i0, (0, 2)), (i0, (0, 0)), "c")]
    (i0, (0, 0))
  = Some
    [((i0, (0, 2)), (i0, (0, 0)), "c");
     ((i0, (0, 1)), (i0, (0, 2)), "b");
     ((i0, (0, 0)), (i0, (0, 1)), "a")].
Proof.
auto.
Qed.

Example AdjacencyListExample10 :
  FindCycle
    [((i0, (0, 0)), (i0, (0, 1)), "a");
     ((i0, (0, 1)), (i0, (0, 2)), "b");
     ((i0, (0, 2)), (i0, (0, 0)), "c")]
  = Some
    [((i0, (0, 1)), (i0, (0, 2)), "b");
     ((i0, (0, 0)), (i0, (0, 1)), "a");
     ((i0, (0, 2)), (i0, (0, 0)), "c")].
Proof.
auto.
Qed.

Example AdjacencyListExample11 :
  FindCycle
    [((i0, (0, 0)), (i0, (0, 1)), "a");
     ((i0, (0, 1)), (i0, (0, 2)), "b");
     ((i0, (0, 2)), (i0, (0, 3)), "c")]
  = None.
Proof.
auto.
Qed.

End AdjacencyListExample.

Record GraphGenerationTraceEntry : Set := mkTraceEntry {
  step : string;
  graphID : nat
}.

Inductive TraceStatus : Set :=
| NormalGraph : TraceStatus
| PrunedGraph : TraceStatus
| InvalidGraph : string -> TraceStatus.

Definition GraphGenerationTrace :=
  (TraceStatus * list GraphGenerationTraceEntry) % type.

Fixpoint StringOfGraphGenerationTraceEntries
  (nl : string)
  (l : list GraphGenerationTraceEntry)
  : string :=
  match l with
  | mkTraceEntry hs hn :: t =>
      StringOf [hs; ": "; stringOfNat hn; nl;
        StringOfGraphGenerationTraceEntries nl t]
  | [] => EmptyString
  end.

Definition StringOfGraphGenerationTrace
  (nl : string)
  (t : GraphGenerationTrace)
  : string :=
  match t with
  | (NormalGraph, l) =>
      StringOf ["NormalGraph"; nl;
        StringOfGraphGenerationTraceEntries nl (rev' l)]
  | (PrunedGraph, l) =>
      StringOf ["Pruned: "; nl;
        StringOfGraphGenerationTraceEntries nl (rev' l)]
  | (InvalidGraph m, l) =>
      StringOf ["Invalid: "; m; ": "; nl;
        StringOfGraphGenerationTraceEntries nl (rev' l)]
  end.

Definition NumberedAdjacencyList := (GraphGenerationTrace * AdjacencyList) % type.
Definition NumberedEdgeList := (GraphGenerationTrace * list GraphEdge) % type.

Definition GraphGenerationStepResult := (TraceStatus * list GraphEdge) % type.
Definition GraphGenerationStepResultAdj := (TraceStatus * AdjacencyList) % type.

Definition KeepGraph
  (keep_pruned : nat)
  (status : TraceStatus)
  : bool :=
  match (status, keep_pruned) with
  | (PrunedGraph, 0) => false
  | (InvalidGraph _, 0) => false
  | (InvalidGraph _, 1) => false
  | _ => true
  end.

Fixpoint GenerateNewTraceEntries
  {A : Type}
  (keep_pruned : nat)
  (l : list (GraphGenerationStepResult * A))
  (name : string)
  (trace : list GraphGenerationTraceEntry)
  (n : nat)
  (l' : list (NumberedEdgeList * A)) (* tail recursion *)
  : list (NumberedEdgeList * A) :=
  let new_trace := mkTraceEntry name n :: trace in
  match l with
  | ((status, g), a) :: t =>
      if KeepGraph keep_pruned status
      then GenerateNewTraceEntries keep_pruned t name trace (S n)
        ((((status, new_trace), g), a) :: l')
      else GenerateNewTraceEntries keep_pruned t name trace (S n) l'
  | [] => l'
  end.

Fixpoint GenerationStepHelper
  {A : Type}
  (keep_pruned : nat)
  (name : string)
  (f : list GraphEdge -> A -> list (GraphGenerationStepResult * A))
  (l : list (NumberedEdgeList * A))
  (l' : list (NumberedEdgeList * A)) (* tail recursion *)
  : list (NumberedEdgeList * A) :=
  match l with
  | ((trace, g), a)::t =>
      match trace with
      | (NormalGraph, l) =>
          let new_entries := GenerateNewTraceEntries keep_pruned (f g a) name l 0 [] in
          GenerationStepHelper keep_pruned name f t (app_rev l' new_entries)
      | _ =>
          GenerationStepHelper keep_pruned name f t (((trace, g), a)::l')
      end
  | [] => l'
  end.

Definition GenerationStep
  {A : Type}
  (keep_pruned : nat)
  (name : string)
  (f : list GraphEdge -> A -> list (GraphGenerationStepResult * A))
  (l : list (NumberedEdgeList * A))
  : list (NumberedEdgeList * A) :=
  GenerationStepHelper keep_pruned name f l [].

Fixpoint GenerateNewTraceEntriesAdj
  {A : Type}
  (keep_pruned : nat)
  (l : list (GraphGenerationStepResultAdj * A))
  (name : string)
  (trace : list GraphGenerationTraceEntry)
  (n : nat)
  (l' : list (NumberedAdjacencyList * A)) (* tail recursion *)
  : list (NumberedAdjacencyList * A) :=
  let new_trace := mkTraceEntry name n :: trace in
  match l with
  | ((status, g), a) :: t =>
      if KeepGraph keep_pruned status
      then GenerateNewTraceEntriesAdj keep_pruned t name trace (S n)
        ((((status, new_trace), g), a) :: l')
      else GenerateNewTraceEntriesAdj keep_pruned t name trace (S n) l'
  | [] => l'
  end.

Fixpoint GenerationStepHelperAdj
  {A : Type}
  (keep_pruned : nat)
  (name : string)
  (f : AdjacencyList -> A -> list (GraphGenerationStepResultAdj * A))
  (l : list (NumberedAdjacencyList * A))
  (l' : list (NumberedAdjacencyList * A)) (* tail recursion *)
  : list (NumberedAdjacencyList * A) :=
  match l with
  | ((trace, g), a)::t =>
      match trace with
      | (NormalGraph, l) =>
          let new_entries := GenerateNewTraceEntriesAdj keep_pruned (f g a) name l 0 [] in
          GenerationStepHelperAdj keep_pruned name f t (app_rev l' new_entries)
      | _ =>
          GenerationStepHelperAdj keep_pruned name f t (((trace, g), a)::l')
      end
  | [] => l'
  end.

Fixpoint GenerationStepAdj
  {A : Type}
  (keep_pruned : nat)
  (name : string)
  (f : AdjacencyList -> A -> list (GraphGenerationStepResultAdj * A))
  (l : list (NumberedAdjacencyList * A))
  : list (NumberedAdjacencyList * A) :=
  GenerationStepHelperAdj keep_pruned name f l [].

Fixpoint PrintGraphGenerationTracesHelper
  {A B C : Type}
  (a : A)
  (l : list ((GraphGenerationTrace * B) * C))
  : A :=
  match l with
  | ((h, _), _)::t =>
      Println (PrintGraphGenerationTracesHelper a t)
        [newline; "Trace: "; newline; StringOfGraphGenerationTrace newline h; newline]
  | [] => a
  end.

Definition PrintGraphGenerationTraces
  {A B : Type}
  (s : string)
  (l : list ((GraphGenerationTrace * A) * B))
  : list ((GraphGenerationTrace * A) * B) :=
  let l := Println l ["Graph Traces at "; s; ": "] in
  PrintGraphGenerationTracesHelper l l.
