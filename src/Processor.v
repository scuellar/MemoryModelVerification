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
Require Import String.
Require Import Arith.
Require Import Debug.
Require Import Util.
Require Import StringUtil.
Require Import Instruction.
Require Import Graph.
Require Import Execution.

Import ListNotations.
Open Scope string_scope.
Open Scope list_scope.  

(** ** Basic Type Definitions *)

Definition PipeID := nat.

(** *** [PerformEdgeInterpretation] *)
(** Given a high-level RF, WS, or FR edge, interpret in the context of the
given [MicroopPath]. *)
Record PerformEdgeInterpretation : Set := mkInterpretation {
  rfInterpretation : (Microop * Microop) -> list (option GraphEdge);
  wsInterpretation : (Microop * Microop) -> list GraphEdge;
  frInterpretation : (Microop * Microop) -> list GraphEdge
}.

(** *** [ExtraConstraint] *)
(** Extra graph constraints added to a path based on the "dynamic" state of
the graph. *)
Inductive ExtraConstraintType : Set :=
| WritesOnly : ExtraConstraintType
| AnyAccess : ExtraConstraintType.

Inductive ExtraConstraint : Set :=
  (** [ReadsBetween]: captures the notion of "reads from some other
  write/access to the same address and data, in between that write/access
  passing through the associated two locations". *)
| ReadsBetween : ExtraConstraintType -> Location -> Location -> Location
    -> ExtraConstraint
  (** [FlushThread]: force all program order-previous accesses of the specified
  type to have reached the specified (first) set of locations before the current
  instruction reaches the specified (second) location *)
| FlushThread : ExtraConstraintType -> list Location -> Location -> ExtraConstraint.

Inductive ViCLSource : Set :=
| InitialState : ViCLSource
| PreSourced : ViCLSource
| SrcViCL : (GraphNode * GraphNode) -> ViCLSource
| CyclicSourcing : ViCLSource.

(** ** Pipeline Definitions *)

(** *** [PropagatedOrdering] *)
(** Orderings propagated from one edge to another edge, i.e., Per-Stage
Reordering Behaviors *)
Definition PropagatedOrdering :=
  ((Location * Location) * (Location * Location)) % type.

(** *** [MicroopPath] *)
(** A possible path through a pipeline, along with any constraints implied by
that path. *)
Record MicroopPath : Set := mkMicroopPath {
  pathName : string;
  pathEdges : list (Location * Location);
  prop : list PropagatedOrdering;
  extraConstraints : list ExtraConstraint;
  performEdges : PerformEdgeInterpretation
}.

(** *** [MicroopPathMap] *)
(** Associate a set of [MicroopPath] constraints with a given [Microop]. *)
Definition MicroopPathMap := list (Microop * MicroopPath).

(** *** [Pipeline] *)
(** Primarily, a [Pipeline] is a mapping from a [Microop] to a list of possible
paths that [Microop] can take through the [Pipeline]. *)
Record Pipeline : Set := mkPipeline {
  pipeName : string;
  pipeID : PipeID;
  viclLevels : list nat;
  possiblePaths : Microop -> list MicroopPath;
  stageNames : list string
}.

(** *** [Processor] *)
(** A [Processor] is just a list of the component [Pipeline]s. *)
Inductive Processor : Set := mkProcessor {
  procName : string;
  srcRest : (option (GraphNode * GraphNode) * (GraphNode * GraphNode)) -> bool;
  pipes : list Pipeline
}.

(** ** Pipeline Definition Helper Functions *)

Fixpoint StraightLineHelper
  (p : PipeID)
  (a : option nat)
  (l : list nat)
  : list (Location * Location) :=
  match (a, l) with
  | (Some a', h::t) => ((p, a'), (p, h)) :: StraightLineHelper p (Some h) t
  | (None   , h::t) =>                      StraightLineHelper p (Some h) t
  | _               => []
  end.

Definition StraightLine
  (p : nat)
  (l : list nat)
  : list (Location * Location) :=
  StraightLineHelper p None l.

(** **** [AddEdgeToExistingNodes] *)
(** Add an edge to the given [AdjacencyList], but only if it is touching
[GraphNode]s which already exist.  In other words, don't create new node(s) by
adding this edge.  Return: the new [AdjacencyList], plus a bool indicating
whether this edge was added (or whether edge was added previously, as indicated
by the corresponding bool input. *)
Definition AddEdgeToExistingNodes
  (nodes : list GraphNode)
  (prev : bool * AdjacencyList)
  (e : GraphEdge)
  : bool * AdjacencyList :=
  match e with
  | (s, d, l) =>
      match (find (beq_node s) nodes, find (beq_node d) nodes) with
      | (Some _, Some _) =>
          let (previously_added, previous_graph) := prev in
          match AdjacencyListAddEdge previous_graph e with
          | (newly_added, new_graph) =>
              (orb previously_added newly_added, new_graph)
          end
      | _ => prev
      end
  end.

(** **** [AddEdgeToExistingNodes'] *)
(** Add an edge to the given [AdjacencyList], but only if it is touching
[GraphNode]s which already exist.  In other words, don't create new node(s) by
adding this edge. *)
Definition AddEdgeToExistingNodes'
  (nodes : list GraphNode)
  (previous_graph : AdjacencyList)
  (e : GraphEdge)
  : AdjacencyList :=
  match e with
  | (s, d, l) =>
      match (find (beq_node s) nodes, find (beq_node d) nodes) with
      | (Some _, Some _) =>
          match AdjacencyListAddEdge previous_graph e with
          | (_, new_graph) => new_graph
          end
      | _ => previous_graph
      end
  end.

(** **** [AddEdgesToExistingNodes] *)
(** Add the list of [GraphEdge]s to the given [AdjacencyList], but only add
each edge if it touches [GraphNode]s which already exist.  In other words,
don't create new node(s) by adding these edges.  Return: the new
[AdjacencyList], plus a bool indicating whether any edges were added. *)
Definition AddEdgesToExistingNodes
  (nodes : list GraphNode)
  (g : AdjacencyList)
  (l_e : list GraphEdge)
  : bool * AdjacencyList :=
  fold_left (AddEdgeToExistingNodes nodes) l_e (false, g).

Definition AddEdgesToExistingNodes'
  (nodes : list GraphNode)
  (g : list GraphEdge)
  (l_e : list GraphEdge)
  : list GraphEdge :=
  let f x := match x with
             | (s, d, l) => match (find (beq_node s) nodes, find (beq_node d) nodes) with
                            | (Some _, Some _) => false
                            | _ => true
                            end
             end in
  app_tail g (removeb f l_e).

(** *** [IsCyclic] *)
(** Return [true] if the given graph is cyclic. *)
Definition IsCyclic
  (a : NumberedAdjacencyList * MicroopPathMap)
  : bool :=
  match a with
  | (((NormalGraph, _), g), _) =>
      match AdjacencyListTopsort g with
      | ReverseTotalOrder _ => false
      | _ => true
      end
  | _ => true
  end.

(** ** Program Order Edges *)

(** **** [ThreadProgramOrderEdges] *)
(** Given a [Thread], return the set of [GraphEdge]s representing program
order: the set of edges from each instruction in the thread to the next,
at stage 0 of the given [Pipeline]. *)
Fixpoint ThreadProgramOrderEdges
  (pipeID : nat)
  (thread : list Microop)
  (edges : list GraphEdge) (* Tail recursion *)
  : list GraphEdge :=
  match thread with
  | h::t =>
      match t with
      | t1::t2 =>
          ThreadProgramOrderEdges pipeID t
            (((h, (pipeID, 0)), (t1, (pipeID, 0)), "PO") :: edges)
      | [] => edges
      end
  | [] => edges
  end.

(** *** [EnumerateProgramOrderEdges] *)
(** Given a [Program], return the set of [GraphEdge]s representing program
order: the set of edges from each instruction in the thread to the next,
at stage 0 of the given [Pipeline]. *)
Fixpoint EnumerateProgramOrderEdges
  (processor : list Pipeline)
  (program : Program)
  (l : list GraphEdge) (* Tail recursion *)
  : list GraphEdge :=
  match (processor, program) with
  | (proc_h :: proc_t, prog_h :: prog_t) =>
      EnumerateProgramOrderEdges proc_t prog_t
        (ThreadProgramOrderEdges (pipeID proc_h) prog_h l)
  | _ => l
  end.

(** ** Path Edges *)

(** **** [MicroopExecutions] *)
(** A [MicroopExecutions] is the list of [MicroopPath]s taken by a list of
[Microop]s in one particular execution. *)
Definition MicroopExecutions := list (Microop * MicroopPath).

(** **** [MicroopPathEdges] *)
(** Calculate the [GraphEdge]s representing the [Microop] following the
specified [MicroopPath] through the [Pipeline]. *)
Fixpoint MicroopPathEdges
  (uop : Microop)
  (path : list (Location * Location))
  (edges : list GraphEdge) (* Tail recursion *)
  : list GraphEdge :=
  match path with
  | (l1, l2) :: t =>
      let new_edge := ((uop, l1), (uop, l2), "path") in
      MicroopPathEdges uop t (new_edge :: edges)
  | [] => edges
  end.

(** **** [ThreadPathExecutions] *)
(** Calculate the set of possible [MicroopExecutions] for a given [Thread] on
a given [Pipeline]. *)
Definition ThreadPathExecutions
  (pipeline : Pipeline)
  (thread : Thread)
  : list MicroopExecutions :=
  let pathFunction := possiblePaths pipeline in 
  let instructionExecutions := Map pathFunction thread in
  let cross_product := CrossProduct instructionExecutions in
  (* Zip: pair microops with their corresponding list of possible executions *)
  Map (Zip thread) cross_product.

(** **** [ProgramPathExecutions] *)
(** Calculate the set of possible [MicroopExecutions] for a given [Program] on
a given [Processor]. *)
Definition ProgramPathExecutions
  (program : Program)
  (processor : list Pipeline)
  : list MicroopExecutions :=
  let TPEUncurry x := ThreadPathExecutions (fst x) (snd x) in
  let thread_executions := Map TPEUncurry (Zip processor program) in
  let program_executions := CrossProduct thread_executions in
  (* fold_left: combine the list of lists of [MicroopExecutions] from each
  [Thread] into a single list of [MicroopExecutions] for the [Program] *)
  Map (fun x => fold_left (app_tail (A:=_)) x []) program_executions.

(** **** [MicroopExecutionEdges] *)
(** Calculate the set of [GraphEdge]s associated with the given [Microop]
and the given [MicroopExecution].  Also, build up a list of taken
[MicroopPath]s so that we can return to them later when the rest of
the graph has been built up. *)
Fixpoint MicroopExecutionEdges
  (edges_cmap : list GraphEdge * MicroopPathMap) (* Tail recursion *)
  (exec : MicroopExecutions)
  : list GraphEdge * MicroopPathMap :=
  let (edges, cmap) := edges_cmap in
  match exec with
  | h::t =>
      match h with
      | (uop, mkMicroopPath _ path_edges _ _ _) =>
          let edges' := MicroopPathEdges uop path_edges edges in
          MicroopExecutionEdges (edges', h :: cmap) t
      end
  | [] => (edges, cmap)
  end.

(** *** [EnumeratePathEdges] *)
(** Given a [Processor] and a [Program], enumerate the set of possible path
executions that can be taken by the [Microop]s in the [Program].  Also take
as input a graph from a previous stage, and use that as the starting point
for the newly-added path edges. *)
Definition EnumeratePathEdges
  (program : Program)
  (processor : Processor)
  (edges : list GraphEdge) (* Tail recursion *)
  : list (list GraphEdge * MicroopPathMap) :=
  let executions := ProgramPathExecutions program (pipes processor) in
  Map (MicroopExecutionEdges (edges, [])) executions.

(** ** Coherence Protocol Edges *)

(** **** [MicroopPathMapFind] *)
(** Find the [MicroopPath] constraints associated with the given [Microop] in
the given [MicroopPathMap]. *)
Fixpoint MicroopPathMapFind
  (c : MicroopPathMap)
  (uop : Microop)
  : option MicroopPath :=
  match c with
  | (h1, h2)::t =>
      if beq_uop h1 uop then Some h2 else MicroopPathMapFind t uop
  | [] => None
  end.

(** **** [ExecutionPerformEdgesWSFold] *)
(** Given a list of nodes in a total order specified by WS for a given address,
add a WS edge to the graph for the first two nodes in the list, according to
the pipeline's specification of how to interpret that edge for the chosen
[MicroopPath], but only add the edge if it connects two pre-existing nodes;
otherwise, just drop the edge silently.  Then recurse with the next two nodes
in the WS list (overlapping the first). *)
Fixpoint ExecutionPerformEdgesWSFold
  (c : MicroopPathMap)
  (nodes : list GraphNode)
  (edges : list GraphEdge)
  (ws : list Microop)
  : list GraphEdge :=
  match ws with
  | h::t =>
      match t with
      | t1::t2 =>
          let w1_nodes := match MicroopPathMapFind c h with
          | Some (mkMicroopPath _ _ _ _ (mkInterpretation _ f _)) => Some (f (h, t1))
          | None => None
          end in
          let w2_nodes := match MicroopPathMapFind c t1 with
          | Some (mkMicroopPath _ _ _ _ (mkInterpretation _ f _)) => Some (f (h, t1))
          | None => None
          end in
          let edges' := match (w1_nodes, w2_nodes) with
          | (Some w1list, Some w2list) =>
            let f x := (fst (fst x), snd (snd x)) in
            let newEdges := Map f (Zip w1list w2list) in
            AddEdgesToExistingNodes' nodes edges newEdges
          | _ => edges
          end in
          ExecutionPerformEdgesWSFold c nodes edges' t
      | [] => edges
      end
  | [] => edges
  end.

(** **** [ExecutionPerformEdgesWS] *)
(** Given a list of WS total orders per address, add edges to the graph
according to the pipeline's specification of how to interpret those edges for
the chosen [MicroopPath]s, but only add the edges if they connect two
pre-existing nodes; otherwise, just drop them silently. *)
Definition ExecutionPerformEdgesWS
  (c : MicroopPathMap)
  (nodes : list GraphNode)
  (edges : list GraphEdge)
  (wss : list (list Microop))
  : list GraphEdge :=
  fold_left (ExecutionPerformEdgesWSFold c nodes) wss edges.

(** ** Propagation of Edges *)

(** **** [PropagateEdgesHelper] *)
(** Given a [PropagatedOrdering] specification, find all edges meeting the
precondition of the propagation, and add the resulting implied edges. *)
Definition PropagateEdgesHelper
  (n : list GraphNode)
  (a : bool * AdjacencyList)
  (p : Microop * PropagatedOrdering)
  : bool * AdjacencyList :=
  match p with
  | (op, (((p0, l0), (p1, l1)), ((p2, l2), (p3, l3)))) =>
      (* If there is an edge from ((op, p0, l0), (op, p1, l1)), then add an edge
         ((op, p2, l2), (op, p3, l3)) *)
      let f e :=
        match e with
        | ((ia, (pa, la)), (ib, (pb, lb)), _) =>
            andb (beq_uop ia op) (andb (andb (beq_nat p0 pa) (beq_nat p1 pb))
              (andb (beq_nat l0 la) (beq_nat l1 lb)))
        end in
      (* Find all edges meeting the specified precondition *)
      let srcs := AdjacencyListFilter f (snd a) in
      (* Replace them with the corresponding implied edge *)
      let replace e :=
        match e with
        | ((ia, (pa, la)), (ib, (pb, lb)), _) =>
            ((ia, (p2, l2)), (ib, (p3, l3)), "propagated")
        end in
      let dsts := Map replace srcs in
      (* Add them to the list (if they touch pre-existing nodes only) *)
      fold_left (AddEdgeToExistingNodes n) dsts a
  end.

Definition GetPropagations
  (c : MicroopPathMap)
  : list (Microop * PropagatedOrdering) :=
  let g y z := (y,z) in
  let f x := Map (g (fst x)) (prop (snd x)) in
  fold_left (app_tail (A:=_)) (Map f c) [].

(** *** [PropagateEdges] *)
(** Find all edges meeting the precondition of the
[PropagatedOrdering]s of each [Microop] in the [Pipeline]s,
and add the resulting implied edges. *)
Definition PropagateEdges
  (a : AdjacencyList)
  (c : MicroopPathMap)
  : list (GraphGenerationStepResultAdj * MicroopPathMap) :=
  let l := GetPropagations c in
  match AdjacencyListTransitiveClosure a with
  | TC a' =>
      let n := NodesFromAdjacencyList a in
      match fold_left (PropagateEdgesHelper n) l (false, a') with
      | (_, l') => [((NormalGraph, l'), c)]
      end
  | _ => [((PrunedGraph, a), c)]
  end.

(** ** Path Constraints *)

(** **** [FilterNodesByAddressData] *)
(** Find [GraphNode]s which access the same [Address] and [Data] as a specified
[GraphNode] and which are passing through a particular ([PipeID], [Location])
point *)
Fixpoint FilterNodesByAddressData
  (mode : ExtraConstraintType)
  (a : Address)
  (d : Data)
  (p0 : PipeID)
  (l0 : nat)
  (l : list GraphNode)
  : list GraphNode :=
  match l with
  | h::t =>
      match (mode, h) with
      |  (AnyAccess, (mkMicroop _ _ _ (Read a' d'), (p', l'))) =>
          if andb
            (andb (beq_nat a a') (beq_nat d d'))
            (andb (beq_nat p' p0) (beq_nat l' l0))
          then h :: FilterNodesByAddressData mode a d p0 l0 t
          else      FilterNodesByAddressData mode a d p0 l0 t
      | (_, (mkMicroop _ _ _ (Write a' d'), (p', l'))) =>
          if andb
            (andb (beq_nat a a') (beq_nat d d'))
            (andb (beq_nat p' p0) (beq_nat l' l0))
          then h :: FilterNodesByAddressData mode a d p0 l0 t
          else      FilterNodesByAddressData mode a d p0 l0 t
      | _ => FilterNodesByAddressData mode a d p0 l0 t
      end
  | [] => []
  end.

(** **** [FilterNodesByAddressLocation] *)
(** Find [GraphNode]s which access the same [Address] as a specified
[GraphNode] and which are passing through a particular ([PipeID], [Location])
point *)
Fixpoint FilterNodesByAddressLocation
  (keep : Microop -> bool)
  (mode : ExtraConstraintType)
  (a : Address)
  (p0 : PipeID)
  (l0 : nat)
  (l : list GraphNode)
  : list GraphNode :=
  match l with
  | h::t =>
      match (mode, h) with
      |  (AnyAccess, (mkMicroop _ _ _ (Read a' d'), (p', l'))) =>
          if andb
            (andb (keep (fst h)) (beq_nat a a'))
            (andb (beq_nat p' p0) (beq_nat l' l0))
          then h :: FilterNodesByAddressLocation keep mode a p0 l0 t
          else      FilterNodesByAddressLocation keep mode a p0 l0 t
      | (_, (mkMicroop _ _ _ (Write a' d'), (p', l'))) =>
          if andb
            (andb (keep (fst h)) (beq_nat a a'))
            (andb (beq_nat p' p0) (beq_nat l' l0))
          then h :: FilterNodesByAddressLocation keep mode a p0 l0 t
          else      FilterNodesByAddressLocation keep mode a p0 l0 t
      | _ => FilterNodesByAddressLocation keep mode a p0 l0 t
      end
  | [] => []
  end.

(** **** [FilterNodesByLocation] *)
(** Find [GraphNode]s which are passing through a particular
([PipeID], [Location]) point *)
Fixpoint FilterNodesByLocation
  (keep : Microop -> bool)
  (mode : ExtraConstraintType)
  (p0 : PipeID)
  (l0 : nat)
  (l : list GraphNode)
  : list GraphNode :=
  match l with
  | h::t =>
      match (mode, h) with
      |  (AnyAccess, (mkMicroop gid _ _ (Read _ _), (p', l'))) =>
          if andb
            (andb (beq_nat p' p0) (beq_nat l' l0))
            (keep (fst h))
          then h :: FilterNodesByLocation keep mode p0 l0 t
          else      FilterNodesByLocation keep mode p0 l0 t
      | (_, (mkMicroop gid _ _ (Write _ _), (p', l'))) =>
          if andb
            (andb (beq_nat p' p0) (beq_nat l' l0))
            (keep (fst h))
          then h :: FilterNodesByLocation keep mode p0 l0 t
          else      FilterNodesByLocation keep mode p0 l0 t
      | _ => FilterNodesByLocation keep mode p0 l0 t
      end
  | [] => []
  end.

(** **** [FindAndRemoveHelper] *)
(** If we find a node [h] such that [f h = true], then remove [h] and return
the rest of the list.  Otherwise, return [None]. *)
Fixpoint FindAndRemoveHelper
  {A : Type}
  (f : A -> bool)
  (l l' : list A)
  : option (list A * A) :=
  match l with
  | h::t =>
      if f h
      then Some (l' ++ t, h)
      else FindAndRemoveHelper f t (l' ++ [h])
  | [] => None
  end.

(** **** [FindAndRemove] *)
(** If we find a node [h] such that [f h = true], then remove [h] and return
the rest of the list.  Otherwise, return [None]. *)
Fixpoint FindAndRemove
  {A : Type}
  (f : A -> bool)
  (l : list A)
  : option (list A * A) :=
  FindAndRemoveHelper f l [].

(** **** [SameInstAs] *)
(** Return [true] if the two [GraphNode]s represent the same [Microop]. *)
Definition SameInstAs
  (x y : GraphNode)
  : bool :=
  match (x, y) with
  | ((ix, _), (iy, _)) => beq_uop ix iy
  end.

(** **** [PairNodesByMicroop] *)
(** Given a list of [GraphNode]s, return the list of pairs of [GraphNode]s for
the same [Microop], and filter out nodes which don't have a partner.  This is
used to find nodes which satisfy the [ExtraConstraint]s associated with a
path. *)
Fixpoint PairNodesByMicroop
  (l_a l_c : list GraphNode)
  (l_pairs : list (GraphNode * GraphNode))
  : list (GraphNode * GraphNode) :=
  match l_a with
  | h::t =>
      match FindAndRemove (SameInstAs h) l_c with
      | Some (l_c', partner) =>
          PairNodesByMicroop t l_c' ((h, partner) :: l_pairs)
      | None => PairNodesByMicroop t l_c l_pairs
      end
  | [] => l_pairs
  end.

(** **** [LaterInPO] *)
(** Return [true] if [a] is later in PO than [b] *)
Fixpoint LaterInPO
  (a b : Microop)
  : bool :=
  bgt_nat (globalID a) (globalID b).

Fixpoint GetCandidateLists
  (uop : Microop)
  (mode : ExtraConstraintType)
  (a : Address)
  (nodes : list GraphNode)
  (loc_list : list Location)
  : list (list GraphNode) :=
  match loc_list with
  | [] => []
  | (p0, l0)::t => 
      let candidates := FilterNodesByAddressLocation (LaterInPO uop) mode a p0 l0 nodes in
      candidates::(GetCandidateLists uop mode a nodes t)
  end.

Fixpoint GetCandidateListsNoAddr
  (uop : Microop)
  (mode : ExtraConstraintType)
  (nodes : list GraphNode)
  (loc_list : list Location)
  : list (list GraphNode) :=
  match loc_list with
  | [] => []
  | (p0, l0)::t => 
      let candidates := FilterNodesByLocation (LaterInPO uop) mode p0 l0 nodes in
      candidates::(GetCandidateListsNoAddr uop mode nodes t)
  end.

Fixpoint FilterCandLists2
  (uop : Microop)
  (to_filter : list GraphNode)
  : list GraphNode :=
  match to_filter with
  | [] => []
  | h::t =>
      let f x := match x with
                 | (u, loc) => beq_uop uop u
                 end in
      removeb f to_filter
  end.

Fixpoint FilterCandLists
  (shallow : list GraphNode)
  (to_filter : list (list GraphNode))
  : list (list GraphNode) :=
  match shallow with
  | [] => to_filter
  | (uop, loc)::t => FilterCandLists t (Map (FilterCandLists2 uop) to_filter)
  end.

Fixpoint KeepShallowest
  (i : nat)
  (cand_lists : list (list GraphNode))
  : list (list GraphNode) :=
  match i, cand_lists with
  | _, [] => []
  | S i', h::t => h::(KeepShallowest i' (FilterCandLists h t))
  | O, h::t => Warning [] ["KeepShallowest - length is 0 but reached end of list!"]
  end.

Definition GetFlushCandidatesRead
  (uop : Microop)
  (mode : ExtraConstraintType)
  (a : Address)
  (nodes : list GraphNode)
  (loc_list : list Location)
  : list GraphNode :=
  let cand_lists := GetCandidateLists uop mode a nodes loc_list in
  fold_left (app (A:=_)) (KeepShallowest (List.length cand_lists) cand_lists) [].

Definition GetFlushCandidatesFence
  (uop : Microop)
  (mode : ExtraConstraintType)
  (nodes : list GraphNode)
  (loc_list : list Location)
  : list GraphNode :=
  let cand_lists := GetCandidateListsNoAddr uop mode nodes loc_list in
  fold_left (app (A:=_)) (KeepShallowest (List.length cand_lists) cand_lists) [].

(** **** [DynamicConstraintsHelper] *)
(** Check if a particular [MicroopPath] constraints requirement is satisfiable.
If so, return the set of graphs representing the ways in which the constraint
can be satisfied, or an empty list if the constraints cannot be satisfied.  If
there are no constraints, return [None]. *)
Definition DynamicConstraintsHelper2
  (nodes : list GraphNode)
  (uop : Microop)
  (c : ExtraConstraint)
  : option (list (list GraphEdge)) :=
  match (uop, c) with
  | (mkMicroop g t n (Read a d), ReadsBetween mode (p0, l0) (p1, l1) (p2, l2)) =>
      let candidates_a := FilterNodesByAddressData mode a d p0 l0 nodes in
      let candidates_c := FilterNodesByAddressData mode a d p2 l2 nodes in
      let candidate_pairs := PairNodesByMicroop candidates_a candidates_c [] in
      let constraintEdges p :=
        [(fst p, (uop, (p1, l1)), "ReadsBetween");
         ((uop, (p1, l1)), snd p, "ReadsBetween")] in
      Some (Map constraintEdges candidate_pairs)
  | (mkMicroop g t n (Read a d), FlushThread mode loc_list (p1, l1)) =>
      let candidates := GetFlushCandidatesRead uop mode a nodes loc_list in
      let constraintEdges p := [(p, (uop, (p1, l1)), "FlushThread")] in
      match candidates with
      | [] => None (* It's fine if there's nothing to actually flush *)
      | _ => Some (Map constraintEdges candidates)
      end
  | (mkMicroop g t n (Write a d), ReadsBetween mode (p0, l0) (p1, l1) (p2, l2)) =>
      let candidates_a := FilterNodesByAddressData mode a d p0 l0 nodes in
      let candidates_c := FilterNodesByAddressData mode a d p2 l2 nodes in
      let candidate_pairs := PairNodesByMicroop candidates_a candidates_c [] in
      let constraintEdges p :=
        [(fst p, (uop, (p1, l1)), "ReadsBetween");
         ((uop, (p1, l1)), snd p, "ReadsBetween")] in
      Some (Map constraintEdges candidate_pairs)
  | (mkMicroop _ _ _ (Fence _), FlushThread mode loc_list (p1, l1)) =>
      let candidates := GetFlushCandidatesFence uop mode nodes loc_list in
      let constraintEdges p := [(p, (uop, (p1, l1)), "FlushThread")] in
      match candidates with
      | [] => None (* It's fine if there's nothing to actually flush *)
      | _ => Some (Map constraintEdges candidates)
      end
  | _ => (* No solution *)
      Some []
  end.

Fixpoint DynamicConstraintsHelper
  (nodes : list GraphNode)
  (uop : Microop)
  (l : list ExtraConstraint)
  (l' : list (list (list GraphEdge))) (* tail recursion *)
  : list (list (list GraphEdge)) :=
  match l with
  | h::t =>
      match DynamicConstraintsHelper2 nodes uop h with
      | Some [] =>
          Println (DynamicConstraintsHelper nodes uop t ([] :: l'))
            ["No solution to constraints!"]
      | Some x => DynamicConstraintsHelper nodes uop t (x :: l')
      | None => DynamicConstraintsHelper nodes uop t l'
      end
  | [] => l'
  end.

(** **** [DynamicConstraintsHelperFold] *)
(** Iterate over the list of [MicroopPath] constraints in a given execution to
make sure they are all satisfied.  [None] means no constraints, [Some x] means
[x] is the list of choices for a particular constraint. *)
Fixpoint DynamicConstraintsHelperFold
  (m : MicroopPathMap)
  (nodes : list GraphNode)
  (l' : list (list (list GraphEdge))) (* tail recursion *)
  : list (list (list GraphEdge)) :=
  match m with
  | (uop, mkMicroopPath _ _ _ cs _)::t =>
      let candidates := DynamicConstraintsHelper nodes uop cs [] in
      DynamicConstraintsHelperFold t nodes (candidates ++ l')
  | [] => l'
  end.

(** *** [EnumerateDynamicConstraints] *)
(** Iterate over the list of [MicroopPath] constraints in a given execution to
find the set of satisfying solutions, and return the set of graphs for each
solution. *)
Definition EnumerateDynamicConstraints
  (g : list GraphEdge)
  (c : MicroopPathMap)
  : list (GraphGenerationStepResult * MicroopPathMap) :=
  let nodes := NodesFromEdges g in
  let edge_candidates := DynamicConstraintsHelperFold c nodes [] in
  let edge_candidates' := CrossProduct edge_candidates in
  let edge_candidates'' :=
    Map (fun x => fold_left (app_tail (A:=_)) x []) edge_candidates' in
  (* If there were no constraints to be satisfied, return the original list.
     If there were, merge each solution with the input graph and return the
     resulting list of graphs. *)
  match (edge_candidates, edge_candidates'') with
  | ([], _) => [((NormalGraph, g), c)]
  | (_, []) => [((InvalidGraph "No solution to constraints", g), c)]
  | (_, _) => Map (fun x => ((NormalGraph, app_tail g x), c)) edge_candidates''
  end.

Fixpoint EdgesFromOrdering
  (ordering : list (GraphNode * GraphNode))
  : list GraphEdge :=
  match ordering with
  | [] => []
  | (c1, i1)::t => match t with
            | [] => []
            | (c2, i2)::t2 => (i1, c2, "ViCLOrdering")::(EdgesFromOrdering t)
            end
  end.

Definition AddNodeOrdering
  (a_c : AdjacencyList * MicroopPathMap)
  (ordering : list (GraphNode * GraphNode))
  : GraphGenerationStepResultAdj * MicroopPathMap :=
  let (a, c) := a_c in
  let edgeList := EdgesFromOrdering ordering in
  let g := snd (AddEdgesToExistingNodes (NodesFromAdjacencyList a) a edgeList) in
  ((NormalGraph, g), c).

Fixpoint FilterNodesByAddress
  (p0 : PipeID)
  (a : Address)
  (l : list GraphNode)
  : list GraphNode :=
  match l with
  | h::t =>
      match h with
      | (mkMicroop _ _ _ (Read a' d'), (p', l')) =>
          if andb (beq_nat a a') (beq_nat p' p0)
          then h :: FilterNodesByAddress p0 a t
          else      FilterNodesByAddress p0 a t
      | (mkMicroop _ _ _ (Write a' d'), (p', l')) =>
          if andb (beq_nat a a') (beq_nat p' p0)
          then h :: FilterNodesByAddress p0 a t
          else      FilterNodesByAddress p0 a t
      | _ => FilterNodesByAddress p0 a t
      end
  | [] => []
  end.

Definition EnumerateViCLLevel
  (pipe : PipeID)
  (level : nat)
  (addr : Address)
  (a_c : GraphGenerationStepResultAdj * MicroopPathMap)
  : list (GraphGenerationStepResultAdj * MicroopPathMap) :=
  let (ta, c) := a_c in
  let (t, a) := ta in
  match t with
  | NormalGraph =>
      match IsCyclic (((NormalGraph, []), a), c) with
      | true => [((PrunedGraph, a), c)]
      | false =>
          let nodes := NodesFromAdjacencyList a in
          let viclcs := FilterNodesByLocation (fun _ => true) AnyAccess pipe level nodes in
          let viclis := FilterNodesByLocation (fun _ => true) AnyAccess pipe (level + 1) nodes in
          let viclcs_filt := FilterNodesByAddress pipe addr viclcs in
          let viclis_filt := FilterNodesByAddress pipe addr viclis in
          let vicls := PairNodesByMicroop viclcs_filt viclis_filt [] in
          let orders := AllPermutations (fun _ => true) vicls in
          match orders with
          | [] => [((NormalGraph, a), c)]
          | _ => Map (AddNodeOrdering (a, c)) orders
          end
      end
  | _ => [a_c]
  end.

Fixpoint EnumerateViCLLevelAddrs
  (pipe : PipeID)
  (level : nat)
  (addrs : list Address)
  (a_c : list (GraphGenerationStepResultAdj * MicroopPathMap))
  : list (GraphGenerationStepResultAdj * MicroopPathMap) :=
  match addrs with
  | [] => a_c
  | h::t => EnumerateViCLLevelAddrs pipe level t
      (fold_left (app (A:=_)) (Map (EnumerateViCLLevel pipe level h) a_c) [])
  end.

Fixpoint EnumerateViCLLevels
  (pipe : PipeID)
  (viclLevels : list nat)
  (addrs : list Address)
  (a_c : list (GraphGenerationStepResultAdj * MicroopPathMap))
  : list (GraphGenerationStepResultAdj * MicroopPathMap) :=
  match viclLevels with
  | [] => a_c
  | h::t => EnumerateViCLLevels pipe t addrs (EnumerateViCLLevelAddrs pipe h addrs a_c)
  end.

Fixpoint EnumeratePipelineViCLsHelper
  (p : list Pipeline)
  (addrs : list Address)
  (a_c : list (GraphGenerationStepResultAdj * MicroopPathMap))
  : list (GraphGenerationStepResultAdj * MicroopPathMap) :=
  match p with
  | [] => a_c
  | h::t => EnumeratePipelineViCLsHelper t addrs (EnumerateViCLLevels (pipeID h) (viclLevels h) addrs a_c)
  end.

Definition EnumeratePipelineViCLs
  (p : list Pipeline)
  (addrs : list Address)
  (a : AdjacencyList)
  (c : MicroopPathMap)
  : list (GraphGenerationStepResultAdj * MicroopPathMap) :=
  EnumeratePipelineViCLsHelper p addrs [((NormalGraph, a), c)].

Fixpoint GetUniqueAddrs
  (l : list Address)
  : list Address :=
  match l with
  | [] => []
  | h::t => let f x := beq_nat h x in
            let dup := fold_left orb (Map f t) false in
            match dup with
            | true => GetUniqueAddrs t
            | false => h::(GetUniqueAddrs t)
            end
  end.

Fixpoint GetAddrs
  (l : list (option Address))
  : list Address :=
  match l with
  | [] => []
  | h::t => match h with
            | Some a => a :: GetAddrs t
            | None => GetAddrs t
            end
  end.

Definition GetAddressList
  (l : list Microop)
  : list Address :=
  let f x := match x with
             | mkMicroop _ _ _ (Read  a _) => Some a
             | mkMicroop _ _ _ (Write a _) => Some a
             | _ => None
             end in
  GetUniqueAddrs (GetAddrs (Map f l)).

(** ** Putting it all together *)

Fixpoint NumberGraphs
  (l : list (list GraphEdge * MicroopPathMap))
  (l' : list (NumberedEdgeList * MicroopPathMap))
  (n : nat)
  : list (NumberedEdgeList * MicroopPathMap) :=
  match l with
  | (g, c) :: t =>
     NumberGraphs t ((((NormalGraph, [mkTraceEntry "Paths" n]), g), c) :: l') (S n)
  | [] => l'
  end.

Definition CalcWSScenarios
  (last_values : list (Address * Data))
  (p : Program)
  : list (list (list Microop)) :=
  let uop_list := fold_left (app_tail (A:=_)) p [] in
  let w := SortWrites uop_list in
  WSScenarios w last_values.

Definition ApplyWSEdges
  (ws_scen : list (list (list Microop)))
  (graph : list GraphEdge)
  (c : MicroopPathMap)
  : list (GraphGenerationStepResult * MicroopPathMap) :=
  let nodes := NodesFromEdges graph in
  let new_els := Map (ExecutionPerformEdgesWS c nodes graph) ws_scen in
  Map (fun x => ((NormalGraph, x), c)) new_els.

Definition FindPipelineViCLTuplesLevel
  (addr : Address)
  (p : PipeID)
  (level : nat)
  (nodes : list GraphNode)
  : list (GraphNode * GraphNode) :=
  let viclcs := FilterNodesByLocation (fun _ => true) AnyAccess p level nodes in
  let viclis := FilterNodesByLocation (fun _ => true) AnyAccess p (level + 1) nodes in
  let viclcs_filt := FilterNodesByAddress p addr viclcs in
  let viclis_filt := FilterNodesByAddress p addr viclis in
  PairNodesByMicroop viclcs_filt viclis_filt [].

Fixpoint FindPipelineViCLTuples
  (addr : Address)
  (p : PipeID)
  (viclLevels : list nat)
  (l : list GraphNode)
  : list (GraphNode * GraphNode) :=
  match viclLevels with
  | [] => []
  | h::t => (FindPipelineViCLTuplesLevel addr p h l) ++ (FindPipelineViCLTuples addr p t l)
  end.

Fixpoint FindViCLTuples
  (addr : Address)
  (p : list Pipeline)
  (l : list GraphNode)
  : list (GraphNode * GraphNode) :=
  match p with
  | [] => []
  | h::t => (FindPipelineViCLTuples addr (pipeID h) (viclLevels h) l) ++ (FindViCLTuples addr t l)
  end.

Fixpoint GetViCLLevels
  (pid : PipeID)
  (p : list Pipeline)
  : list nat :=
  match p with
  | [] => Warning [] ["Undefined pipe ID!"]
  | h::t => if beq_nat pid (pipeID h) then viclLevels h else GetViCLLevels pid t
  end.

Fixpoint EdgeFromViCL
  (viclLevels : list nat)
  (loc : nat)
  : option bool :=
  match viclLevels with
  | [] => None
  | h::t => if (beq_nat loc h) then Some true
            else if (beq_nat loc (h + 1)) then Some false
            else EdgeFromViCL t loc
  end.

Definition GetSourceViCL
  (src_is_create : bool)
  (s : GraphNode)
  : option (GraphNode * GraphNode) :=
  match s with
  | (uop, (pid, loc)) => if src_is_create then Some (s, (uop, (pid, loc + 1))) else Some ((uop, (pid, loc - 1)), s)
  end.

Fixpoint FindExistingSourceViCL
  (p : list Pipeline)
  (vicl : (GraphNode * GraphNode))
  (edges : list GraphEdge)
  : option (option (GraphNode * GraphNode) * (GraphNode * GraphNode)) :=
  let (c, i) := vicl in
  match edges with
  | [] => None
  | (s, d, l)::t => if beq_string l "path" then
                        let (uop, pl) := s in
                        let (pid, loc) := pl in
                        (* There should only be one path edge incoming to a ViCL_Create. *)
                        let edge_type := EdgeFromViCL (GetViCLLevels pid p) loc in
                        match edge_type with
                        | None => None
                        | Some x => Some (GetSourceViCL x s, vicl)
                        end
                    else FindExistingSourceViCL p vicl t
  end.

Fixpoint FindUnsourcedViCLs
  (el : list GraphEdge)
  (p : list Pipeline)
  (vicls : list (GraphNode * GraphNode))
  (unsourced_vicls : list (GraphNode * GraphNode))
  (existing_srcs : list (option (GraphNode * GraphNode) * (GraphNode * GraphNode)))
  : (list (option (GraphNode * GraphNode) * (GraphNode * GraphNode))) * list (GraphNode * GraphNode) :=
  match vicls with
  | [] => (existing_srcs, unsourced_vicls)
  | h::t => let (c, i) := h in
            let f x := match x with
            | (s, d, l) => negb (beq_node c d)
            end in
            match removeb f el with
            | [] => FindUnsourcedViCLs el p t (h::unsourced_vicls) existing_srcs
            | l => match FindExistingSourceViCL p h l with
                   | None => FindUnsourcedViCLs el p t unsourced_vicls existing_srcs
                   | Some y => FindUnsourcedViCLs el p t unsourced_vicls (y::existing_srcs)
                   end
            end
  end.

Fixpoint FilterViCLsByData
  (all_vicls : list (GraphNode * GraphNode))
  (data : nat)
  : list (GraphNode * GraphNode) :=
  match all_vicls with
  | [] => []
  | h::t => let (n1, n2) := h in
            let (uop, loc) := n1 in
            let vicl_data := match uop with
            | mkMicroop _ _ _ (Read  _ d) => Some d
            | mkMicroop _ _ _ (Write _ d) => Some d
            | _ => None
            end in
            match vicl_data with
            | Some d => if beq_nat data d then h::(FilterViCLsByData t data) else FilterViCLsByData t data
            | None => []
            end
  end.

Definition GetViCLSourceList
  (all_vicls : list (GraphNode * GraphNode))
  (to_src : GraphNode)
  : list (option (GraphNode * GraphNode)) :=
  let (uop, loc) := to_src in
  let data := match uop with
  | mkMicroop _ _ _ (Read _ d) => Some d
  | _ => None
  end in
  match data with
  | Some d => let f x := match x with
                         | (n1, n2) => beq_node to_src n1 (* Can't source yourself. *)
                         end in
              let real_srcs := removeb f (FilterViCLsByData all_vicls d) in
              let g y := Some y in
              let real_opt_srcs := Map g real_srcs in
              (* Add the case where the op reads from the initial state, if applicable. *)
              if beq_nat O d then (None::real_opt_srcs) else real_opt_srcs
  | None => []
  end.

Fixpoint GetViCLSourceLists
  (all_vicls : list (GraphNode * GraphNode))
  (unsourced : list (GraphNode * GraphNode))
  : list (list (option (GraphNode * GraphNode) * (GraphNode * GraphNode))) :=
  match unsourced with
  | [] => []
  | h::t => let (c, i) := h in
            let f x y := (y, x) in
            (Map (f h) (GetViCLSourceList all_vicls c))::(GetViCLSourceLists all_vicls t)
  end.

Fixpoint FilterSourceList
  (src_rest : (option (GraphNode * GraphNode) * (GraphNode * GraphNode)) -> bool)
  (source_list : list (option (GraphNode * GraphNode) * (GraphNode * GraphNode)))
  : list (option (GraphNode * GraphNode) * (GraphNode * GraphNode)) :=
  match source_list with
  | [] => []
  | h::t => if src_rest h then h::(FilterSourceList src_rest t) else FilterSourceList src_rest t
  end.

Definition FilterSourceLists
  (src_rest : (option (GraphNode * GraphNode) * (GraphNode * GraphNode)) -> bool)
  (source_lists : list (list (option (GraphNode * GraphNode) * (GraphNode * GraphNode))))
  : list (list (option (GraphNode * GraphNode) * (GraphNode * GraphNode))) :=
  Map (FilterSourceList src_rest) source_lists.

Fixpoint AllViCLsSourceable
  (source_lists : list (list (option (GraphNode * GraphNode) * (GraphNode * GraphNode))))
  : bool :=
  match source_lists with
  | [] => true
  | h::t => match h with
            | [] => false (* The ViCL in question is not sourceable. *)
            | _  => AllViCLsSourceable t
            end
  end.

Definition beq_node_tuple
  (t1 t2 : (GraphNode * GraphNode))
  : bool :=
  match t1, t2 with
  | (n1, n2), (n3, n4) => andb (beq_node n1 n3) (beq_node n2 n4)
  end.

Fixpoint FindSource
  (vicl : option (GraphNode * GraphNode))
  (scenario : list (option (GraphNode * GraphNode) * (GraphNode * GraphNode)))
  : ViCLSource :=
  match vicl with
  | None => InitialState
  | Some v =>
      match scenario with
      | [] => PreSourced (* This ViCL isn't in the scenario given i.e. it's a ViCL that was pre-sourced. *)
      | h::t => match h with
                | (Some s, d) => if beq_node_tuple d v then SrcViCL s else FindSource vicl t
                | (None, d) => if beq_node_tuple d v then InitialState else FindSource vicl t
                end
      end
  end.

Fixpoint FindRootSource
  (vicl : option (GraphNode * GraphNode))
  (scenario : list (option (GraphNode * GraphNode) * (GraphNode * GraphNode)))
  (existing_sourcings : list (option (GraphNode * GraphNode) * (GraphNode * GraphNode)))
  (i : nat)
  : ViCLSource :=
  match i, (FindSource vicl scenario) with
  | _, InitialState => InitialState
  | _, PreSourced => match (FindSource vicl existing_sourcings) with
                     | SrcViCL v => match i with
                                    | S i' => FindRootSource (Some v) scenario existing_sourcings i'
                                    | O => CyclicSourcing
                                    end
                     | PreSourced => match vicl with
                                     | None => Warning InitialState ["Empty ViCL claimed to be pre-sourced!"]
                                     | Some v => SrcViCL v
                                     end
                     | InitialState => Warning InitialState ["Existing sourcing returned initial state!"]
                     | CyclicSourcing => Warning CyclicSourcing ["FindSource returned cyclic sourcing for existing sourcings!"]
                     end
  | S i', SrcViCL v => FindRootSource (Some v) scenario existing_sourcings i'
  | O, SrcViCL v => CyclicSourcing
  | _, CyclicSourcing => Warning InitialState ["FindSource returned CyclicSourcing!"]
  end.

Fixpoint FilterInvalidSrc3
  (scenario : list (option (GraphNode * GraphNode) * (GraphNode * GraphNode)))
  (sourcing : option (GraphNode * GraphNode) * (GraphNode * GraphNode))
  (seen : list (GraphNode * GraphNode))
  (i : nat)
  : bool :=
  match i, sourcing with
  | S i', (Some (n1, n2), (n3, n4)) =>
      match find (beq_node_tuple (n1, n2)) seen with
      | Some _ => false (* cycle of dependencies in the sourcings *)
      | None => let f x := match x with
                           | (tup1, tup2) => beq_node_tuple (n1, n2) tup2
                           end in
                match (find f scenario) with
                | Some y => FilterInvalidSrc3 scenario y ((n3, n4)::seen) i'
                | None => Warning true ["Could not find ViCL source in scenario list!"]
                end
      end
  | _, (None, _) => true
  | _, _ => Warning true ["Catch-all case in FilterInvalidSrc3 triggered!"]
  end.

Fixpoint FilterInvalidSrc2
  (scenario : list (option (GraphNode * GraphNode) * (GraphNode * GraphNode)))
  (sourcings : list (option (GraphNode * GraphNode) * (GraphNode * GraphNode)))
  (ret : list (option (GraphNode * GraphNode) * (GraphNode * GraphNode)))
  : list (option (GraphNode * GraphNode) * (GraphNode * GraphNode)) :=
  match sourcings with
  | [] => ret
  (* The longest chain possible should be the length of [scenario]. *)
  | h::t => let (s, d) := h in
            match FindRootSource s scenario [] (List.length scenario) with
            | CyclicSourcing => []
            | _ => FilterInvalidSrc2 scenario t (h::ret)
            end
  end.

Definition FilterInvalidSrc
  (scenario : list (option (GraphNode * GraphNode) * (GraphNode * GraphNode)))
  : list (option (GraphNode * GraphNode) * (GraphNode * GraphNode)) :=
  FilterInvalidSrc2 scenario scenario [].

Definition FilterInvalidSourcings
  (l : list (list (option (GraphNode * GraphNode) * (GraphNode * GraphNode))))
  : list (list (option (GraphNode * GraphNode) * (GraphNode * GraphNode))) :=
  let f x := match x with
               | [] => true
               | _ => false
               end in
  removeb f (Map FilterInvalidSrc l).

(* Note: This currently relies on the WS/SW edges going to all ViCLs of the next write rather than just
   the first one and getting the rest by transitivity... *)
Definition FindSWDestNodes
  (al : AdjacencyList)
  (src : GraphNode)
  : list GraphNode :=
  let f x := match x with
             | (n, str) => negb (beq_string str "WS")
             end in
  let g y := match y with
             | (p, q) => p
             end in
  Map g (removeb f (AdjacencyListGetDsts al src)).

Definition GetAllViCLInvNodes
  (vicls : list (GraphNode * GraphNode))
  (d_c : GraphNode)
  : list GraphNode :=
  let (uop, loc) := d_c in
  let f x := match x with
             | ((n1op, n1loc), (n2op, n2loc)) => negb (beq_uop n1op uop)
             end in
  let g y := match y with
             | (c, i) => i
             end in
  Map g (removeb f vicls).

Fixpoint ConvertToEdgesHelper2
  (nodes : list GraphNode)
  : list GraphEdge :=
  match nodes with
  | [] => []
  | h1::t1 => match t1 with
              | [] => []
              | h2::t2 => (h1, h2, "FR")::(ConvertToEdgesHelper2 t2)
              end
  end.

Fixpoint ConvertToEdgesHelper
  (vicls : list (GraphNode * GraphNode))
  (al : AdjacencyList)
  (scenario : list (option (GraphNode * GraphNode) * (GraphNode * GraphNode)))
  (sources : list (option (GraphNode * GraphNode) * (GraphNode * GraphNode)))
  (first_write_c_nodes : list GraphNode)
  (existing_sourcings : list (option (GraphNode * GraphNode) * (GraphNode * GraphNode)))
  : list GraphEdge :=
  match sources with
  | [] => []
  | h::t => let (s, d) := h in
        let (d_c, d_i) := d in
        (* We're guaranteed to find a root source because this is a
        valid sourcing scenario (no cycles). *)
        let rs := FindRootSource s scenario existing_sourcings ((List.length scenario)) in
        match rs with
        | InitialState => let op_vicl_i_nodes := GetAllViCLInvNodes vicls d_c in
                  let fr_tuples := CrossProduct (op_vicl_i_nodes::[first_write_c_nodes]) in
                  let fr_edges := fold_left (app_rev (A:=_)) (Map ConvertToEdgesHelper2 fr_tuples) [] in
                  let fr_plus_rec := fr_edges ++ (ConvertToEdgesHelper vicls al scenario t first_write_c_nodes existing_sourcings) in
                  match s with
                  (* No RF edge. *)
                  | None => fr_plus_rec
                  (* Include the RF edge. *)
                  | Some (s_c, s_i) => let source_edge := (s_c, d_c, "RF") in
                                       source_edge::fr_plus_rec
                  end
        | SrcViCL (rs_c, rs_i) =>
                  let sw_nodes := FindSWDestNodes al rs_i in
                  let op_vicl_i_nodes := GetAllViCLInvNodes vicls d_c in
                  let fr_tuples := CrossProduct (op_vicl_i_nodes::[sw_nodes]) in
                  let fr_edges := fold_left (app_rev (A:=_)) (Map ConvertToEdgesHelper2 fr_tuples) [] in
                  let fr_plus_rec := fr_edges ++ (ConvertToEdgesHelper vicls al scenario t first_write_c_nodes existing_sourcings) in
                  match s with
                  | None => Warning [] ["Root source is actual store but actual source is initial state!"]
                  | Some (s_c, s_i) => let source_edge := (s_c, d_c, "RF") in
                                       source_edge::fr_plus_rec
                  end
        | CyclicSourcing => Warning [] ["Found a cyclic sourcing while converting to edges!"]
        | PreSourced => Warning [] ["FindRootSource returned PreSourced!"]
       end
  end.

Definition ConvertToEdges
  (vicls : list (GraphNode * GraphNode))
  (al : AdjacencyList)
  (first_write_c_nodes : list GraphNode)
  (existing_sourcings : list (option (GraphNode * GraphNode) * (GraphNode * GraphNode)))
  (scenario : list (option (GraphNode * GraphNode) * (GraphNode * GraphNode)))
  : list GraphEdge :=
  ConvertToEdgesHelper vicls al scenario scenario first_write_c_nodes existing_sourcings.

Fixpoint GetFirstWriteViCLCreateNodesHelper
  (st_vicls : list (GraphNode * GraphNode))
  (al : AdjacencyList)
  : list GraphNode :=
  let g y := match y with
             | (n, str) => negb (beq_string str "WS")
             end in
  match st_vicls with
  | [] => []
  | h::t => let (vc, vi) := h in
            let sw_in_edges := removeb g (AdjacencyListGetDsts al vc) in
            match sw_in_edges with
            | [] => vc::(GetFirstWriteViCLCreateNodesHelper t al)
            | _ => GetFirstWriteViCLCreateNodesHelper t al
            end
  end.

Definition GetFirstWriteViCLCreateNodes
  (vicls : list (GraphNode * GraphNode))
  (al : AdjacencyList)
  : list GraphNode :=
  let f x := match x with
             | (((mkMicroop _ _ _ (Write _ _)), _), (_, _)) => false
             | _ => true
             end in
  let st_vicls := removeb f vicls in
  GetFirstWriteViCLCreateNodesHelper st_vicls al.

Definition EnumerateViCLSourcesAddr2
  (addr : Address)
  (src_rest : (option (GraphNode * GraphNode) * (GraphNode * GraphNode)) -> bool)
  (p : list Pipeline)
  (el : list GraphEdge)
  (c : MicroopPathMap)
  : list (GraphGenerationStepResult * MicroopPathMap) :=
  let nodes := NodesFromEdges el in
  (* First find all ViCL tuples, and then all ViCL tuples that need sourcing. *)
  let vicls := FindViCLTuples addr p nodes in
  let (existing_sourcings, unsourced_vicls) := FindUnsourcedViCLs el p vicls [] [] in
  (* Only proceed if there are ViCL tuples that need to be sourced. Otherwise just
     return the original graph. *)
  let f x := match x with
             | [] => true
             | _ => false
             end in
  if f unsourced_vicls then [((NormalGraph, el), c)] else
  (* Find all possible sources for the ViCLs. *)
  let source_lists := GetViCLSourceLists vicls unsourced_vicls in
  let good_source_lists := FilterSourceLists src_rest source_lists in
  (* Enumerate all combinations of sources for the ViCLs. *)
  match AllViCLsSourceable good_source_lists with
  | true => let scenario_lists := CrossProduct good_source_lists in
            let filt_lists := FilterInvalidSourcings scenario_lists in
            let flipped_al := AdjacencyListFromEdges (Map ReverseEdge el) in
            let first_write_vcs := GetFirstWriteViCLCreateNodes vicls flipped_al in
            let edge_lists := Map (ConvertToEdges vicls (AdjacencyListFromEdges el) first_write_vcs existing_sourcings) filt_lists in
            (* The ViCL sourcing relations are generated through searches of the nodes in
               the graph. Thus, there is no way that any of the edges we have to add will result
               in new nodes being added to the graph. As such, we can just append the new edges
               to the current edges. *)
            let new_edge_lists := Map (app_tail el) edge_lists in
            let g y := match y with
                       | el' => ((NormalGraph, el'), c)
                       end in
                       Map g new_edge_lists
  | false => [((InvalidGraph "ViCLs not all sourceable", el), c)]
  end.

Fixpoint EnumerateViCLSourcesAddr
  (p : list Pipeline)
  (src_rest : (option (GraphNode * GraphNode) * (GraphNode * GraphNode)) -> bool)
  (addr : Address)
  (graphs : list (GraphGenerationStepResult * MicroopPathMap))
  (l : list (GraphGenerationStepResult * MicroopPathMap)) (* tail recursion *)
  : list (GraphGenerationStepResult * MicroopPathMap) :=
  match graphs with
  | [] => l
  | ((tr, g), c)::t =>
      match tr with
      | NormalGraph => EnumerateViCLSourcesAddr p src_rest addr t
          (app_rev l (EnumerateViCLSourcesAddr2 addr src_rest p g c))
      | _ => EnumerateViCLSourcesAddr p src_rest addr t (((tr, g), c) :: l)
      end
  end.

Fixpoint EnumerateViCLSourcesHelper
  (p : list Pipeline)
  (src_rest : (option (GraphNode * GraphNode) * (GraphNode * GraphNode)) -> bool)
  (addrs : list Address)
  (graphs : list (GraphGenerationStepResult * MicroopPathMap))
  : list (GraphGenerationStepResult * MicroopPathMap) :=
  match addrs with
  | [] => graphs
  | h::t => EnumerateViCLSourcesHelper p src_rest t (EnumerateViCLSourcesAddr p src_rest h graphs [])
  end.

Definition EnumerateViCLSources
  (p : list Pipeline)
  (src_rest : (option (GraphNode * GraphNode) * (GraphNode * GraphNode)) -> bool)
  (addrs : list Address)
  (graph : list GraphEdge)
  (c : MicroopPathMap)
  : list (GraphGenerationStepResult * MicroopPathMap) :=
  EnumerateViCLSourcesHelper p src_rest addrs [((NormalGraph, graph), c)].

Definition ConvertToNumberedAL
  (g : NumberedEdgeList * MicroopPathMap)
  : NumberedAdjacencyList * MicroopPathMap :=
  match g with
  | ((tr, el), c) => ((tr, AdjacencyListFromEdges el), c)
  end.

(** *** [ProgramGraphs] *)
(** Calculate the set of graphs representing the possible executions of the
given [Program] on the given [Processor]. *)
Definition ProgramGraphs
  (keep_pruned : nat)
  (last_values : list (Address * Data))
  (processor : Processor)
  (program : Program)
  : list (NumberedAdjacencyList * MicroopPathMap) :=
  let po_edges := EnumerateProgramOrderEdges (pipes processor) program [] in
  let po_path_edges := EnumeratePathEdges program processor po_edges in
  (* list (list GraphEdge * MicroopPathMap) *)
  let po_path_adjs_nodes := NumberGraphs po_path_edges [] 0 in
  (* list (AdjacencyList * list GraphNode * MicroopPathMap) *)
  let constrained_graphs := GenerationStep keep_pruned "Constraints"
    EnumerateDynamicConstraints po_path_adjs_nodes in
  let ws_scenarios := CalcWSScenarios last_values program in
  let po_path_ws_adjs := GenerationStep keep_pruned "WS"
    (ApplyWSEdges ws_scenarios) constrained_graphs in
  let addr_list := GetAddressList (fold_left (app_rev (A:=_)) program []) in
  let po_path_cache_els := GenerationStep keep_pruned "ViCLSources"
    (EnumerateViCLSources (pipes processor) (srcRest processor) addr_list) po_path_ws_adjs in
  let po_path_cache_adjs := Map ConvertToNumberedAL po_path_cache_els in
  let po_path_cache_prop_adjs := GenerationStepAdj keep_pruned "Propagate"
    PropagateEdges po_path_cache_adjs in
  (* list (AdjacencyList * MicroopPathMap) *)
  let r := GenerationStepAdj keep_pruned "PipelineViCLs"
    (EnumeratePipelineViCLs (pipes processor) addr_list)
    po_path_cache_prop_adjs in
  match r with
  | [] => Warning r ["No graphs for program!"]
  | _ => r
  end.

(** ** Cyclic Check *)

(** *** [IsObservable] *)
(** Check whether there is any observable execution of a given [Program] on a
given [Processor] (i.e., whether there is some non-cyclic execution. *)
Definition IsObservable
  (graphs : list (NumberedAdjacencyList * MicroopPathMap))
  : bool :=
  negb (fold_left andb (Map IsCyclic graphs) true).

