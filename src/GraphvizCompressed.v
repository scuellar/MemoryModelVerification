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
Require Import Ascii.
Require Import Util.
Require Import StringUtil.
Require Import Instruction.
Require Import Graph.
Require Import Processor.

Import ListNotations.
Open Scope string_scope.

Definition StageName
  (processor : Processor)
  (n : GraphNode)
  : string :=
  match n with
  | (_, (p, l)) =>
      match nth_error (pipes processor) p with
      | Some (mkPipeline _ _ _ _ names) =>
          match nth_error names l with
          | Some s => s
          | None => StringOf ["Loc "; stringOfNat l]
          end
      | None => StringOf ["Loc "; stringOfNat l]
      end
  end.

(** Safe to pass the empty list as the processor - the names that appear in the
graphviz output just won't be as helpful.  *)
Definition GraphvizPrettyStringOfGraphNode
  (node : GraphNode)
  : string :=
  match node with
  | (mkMicroop g t n a, (p, l)) =>
      StringOf [
          "Inst ";
          stringOfNat g;
          ":";
          stringOfNat t;
          ":";
          stringOfNat n;
          "\n";
          GraphvizStringOfMemoryAccess ":" a;
          "\n"
      ]
  end.

Definition GraphvizNodeXPosition
  (n : GraphNode)
  : string :=
  stringOfNat ((globalID (fst n) + threadID (fst n)) + 1).

Definition GraphvizStringOfGraphNode
  (processor : Processor)
  (props : string)
  (n : GraphNode)
  : string :=
  StringOf [tab; GraphvizShortStringOfGraphNode n; " [shape=circle;label=";
    quote; quote; ";"; "pos="; quote; GraphvizNodeXPosition n; ",-";
    stringOfNat (snd (snd n)); "!"; quote; ";";
    props; "];";
    newline].

Definition GraphvizColorForEdgeLabelHelper
  (label : string)
  : string :=
  let f x := beq_string label (fst x) in
  let label_colors := [
    ("PO", "color=blue;");
    ("RF", "color=red;");
    ("WS", "color=orange;");
    ("FR", "color=brown;");
    ("propagated", "color=green;");
    ("path", "color=black;")] in
  match find f label_colors with
  | Some z => snd z
  | None => "color=purple;"
  end.

(** Reuse the "color=" part: e.g., "color=purple;fontcolor=purple". *)
Definition GraphvizColorForEdgeLabel
  (label : string)
  : string :=
  let c := GraphvizColorForEdgeLabelHelper label in
  StringOf [c; "font"; c].

Definition GraphvizTextLabel
  (label : string)
  : string :=
  let f x := beq_string label x in
  let dont_label := ["PO"; "propagated"; "path"] in
  match find f dont_label with
  | Some z => EmptyString
  | None => StringOf ["label="; quote; label; quote; ";"]
  end.

Definition GraphvizStringOfGraphEdge
  (bold : list GraphEdge)
  (props : string)
  (e : GraphEdge)
  : string :=
  match e with
  | (s, d, label) =>
    let constraint :=
      if orb
        (beq_nat (globalID (fst s)) (globalID (fst d)))
        (andb
          (beq_nat 0 (snd (snd s)))
          (beq_nat 0 (snd (snd s))))
      then EmptyString
      else "constraint=false;"
    in
    let color := GraphvizColorForEdgeLabel label in
    let thickness :=
      if existsb (beq_edge e) bold
      then "penwidth=5;"
      else EmptyString
    in
    let textlabel := GraphvizTextLabel label in
    StringOf [
      tab; GraphvizShortStringOfGraphNode s; " -> ";
      GraphvizShortStringOfGraphNode d; " ["; textlabel;
      constraint; color; thickness; props; "];"; newline]
  end.

Definition GraphvizEdges
  (l : list GraphEdge)
  (bold : list GraphEdge)
  : list string :=
  Map (GraphvizStringOfGraphEdge bold "") l.

Fixpoint SortNodesByThread
  (l : list GraphNode)
  (l' : list (list GraphNode))
  : list (list GraphNode) :=
  match l with
  | h::t => SortNodesByThread t (AppendToNth l' (globalID (fst h)) h)
  | [] => l'
  end.

Definition GraphvizNodeCluster
  (processor : Processor)
  (l : list GraphNode)
  (id : nat)
  : list string :=
  fold_left (app (A:=_)) [
    [tab; "subgraph cluster_thread"; stringOfNat id; " {"; newline];
    Map (GraphvizStringOfGraphNode processor "") l;
    [tab; "};"; newline]] [].

Fixpoint GraphvizNodeClusters
  (processor : Processor)
  (l : list (list GraphNode))
  (id : nat)
  : list string :=
  match l with
  | h::t =>
      app (A:=_) (GraphvizNodeCluster processor h id)
        (GraphvizNodeClusters processor t (S id))
  | [] => []
  end.

Fixpoint GraphvizNodesAtFetchHelper
  (l l' : list GraphNode)
  : list GraphNode :=
  match l with
  | h::t =>
      match h with
      | (_, (_, 0)) => GraphvizNodesAtFetchHelper t (h :: l')
      | _           => GraphvizNodesAtFetchHelper t l'
      end
  | [] => l'
  end.

Fixpoint GraphvizNodesAtFetch
  (l : list GraphNode)
  : list GraphNode :=
  GraphvizNodesAtFetchHelper l [].

Fixpoint SetNthToMin
  (l : list (option nat))
  (p v : nat)
  : list (option nat) :=
  match (l, p) with
  | (Some h::t, 0   ) => Some (min h v) :: t
  | (Some h::t, S p') => Some h :: SetNthToMin t p' v
  | (None  ::t, 0   ) => Some v :: t
  | (None  ::t, S p') => None :: SetNthToMin t p' v
  | ([]       , 0   ) => [Some v]
  | ([]       , S p') => None :: SetNthToMin [] p' v
  end.

Module SetNthToMinExample.

Example e1: SetNthToMin [None; Some 2] 0 1 = [Some 1; Some 2].
Proof.
auto.
Qed.

Example e2: SetNthToMin [None; Some 2] 1 1 = [None; Some 1].
Proof.
auto.
Qed.

Example e3: SetNthToMin [None; Some 2] 1 3 = [None; Some 2].
Proof.
auto.
Qed.

End SetNthToMinExample.

Fixpoint GraphvizPipelineLabelXPositionHelper
  (l : list GraphNode)
  (l' : list (option nat))
  : list (option nat) :=
  match l with
  | h::t =>
      GraphvizPipelineLabelXPositionHelper t
        (SetNthToMin l' (threadID (fst h))
          (globalID (fst h) + (threadID (fst h))))
  | [] => l'
  end.

Fixpoint GraphvizPipelineLabelXPositions
  (l : list GraphNode)
  : list (option nat) :=
  GraphvizPipelineLabelXPositionHelper l [].

Fixpoint GetNthFromOptionList
  {A : Type}
  (l : list (option A))
  (n : nat)
  : option A :=
  match (l, n) with
  | (h::t, 0   ) => h
  | (h::t, S n') => GetNthFromOptionList t n'
  | _            => None
  end.

Fixpoint GraphvizLocationLabelStringsHelper3
  (x n : nat)
  (l l' : list string)
  : list string :=
  match l with
  | h::t =>
    GraphvizLocationLabelStringsHelper3 x (S n) t (
      StringOf [tab; "l"; stringOfNat x; "_"; stringOfNat n; "_label [label=";
        quote; h; quote; ";pos="; quote; stringOfNat x; ",-"; stringOfNat n;
        "!"; quote; ";shape=none];"; newline] :: l')
  | [] => l'
  end.

Fixpoint GraphvizLocationLabelStringsHelper2
  (pipeline : Pipeline)
  (l : list (option nat))
  : list string :=
  match GetNthFromOptionList l (pipeID pipeline) with
  | Some x => GraphvizLocationLabelStringsHelper3 x 0 (stageNames pipeline) []
  | None => []
  end.

Fixpoint GraphvizLocationLabelStringsHelper
  (processor : list Pipeline)
  (l : list (option nat))
  (l' : list string)
  : list string :=
  match processor with
  | h::t =>
      GraphvizLocationLabelStringsHelper t l
        (GraphvizLocationLabelStringsHelper2 h l ++ l')
  | [] => l'
  end.

Definition GraphvizLocationLabels
  (processor : list Pipeline)
  (l : list GraphNode)
  : list string :=
  let l' := GraphvizPipelineLabelXPositions l in
  GraphvizLocationLabelStringsHelper processor l' [].

Fixpoint GraphvizNodeLabelString
  (n : GraphNode)
  : string :=
  StringOf [tab; "n"; stringOfNat (globalID (fst n)); "_label [label=";
    quote; GraphvizPrettyStringOfGraphNode n; quote; ";pos="; quote;
    GraphvizNodeXPosition n; ",0.5!"; quote; ";shape=none];"; newline].

Fixpoint GraphvizNodeLabels
  (l : list GraphNode)
  : list string :=
  Map GraphvizNodeLabelString (GraphvizNodesAtFetch l).

Definition GraphvizNodes
  (processor : Processor)
  (l : list GraphNode)
  : list string :=
  fold_left (app (A:=_)) [
    (Map (GraphvizStringOfGraphNode processor EmptyString) l);
    (GraphvizNodeLabels l);
    (GraphvizLocationLabels (pipes processor) l)] [].

Fixpoint StringOfPipelineNames
  (processor : list Pipeline)
  : string :=
  match processor with
  | h::t =>
      match t with
      | [] => (* last pipeline *)
          StringOf [pipeName h; "\n"]
      | _ => append (StringOf [pipeName h; "; "]) (StringOfPipelineNames t)
      end
  | [] => "(no pipelines)"
  end.

Fixpoint StringOfProcessor
  (processor : Processor)
  : string :=
  StringOf ["Processor: "; procName processor; "\n";
    StringOfPipelineNames (pipes processor)].

Fixpoint StringOfPathNames
  (pathmap : MicroopPathMap)
  : string :=
  match pathmap with
  | (uop, path)::t =>
      append (StringOf [
        "Path for instruction "; stringOfNat (globalID uop); ":";
          GraphvizStringOfMemoryAccess "=" (access uop); ": ";
          pathName path; "\n"])
        (StringOfPathNames t)
  | [] => "\n"
  end.

Definition StringOfTrace
  (t : GraphGenerationTrace)
  (bold_edges : list GraphEdge)
  : string :=
  StringOf ["Trace: "; StringOfGraphGenerationTrace "\n" t;
    match bold_edges with
    | h::t => "cycle"
    | [] => "nocycle"
    end
  ].

Definition GraphvizTitle
  (processor : Processor)
  (pathmap : MicroopPathMap)
  (trace : GraphGenerationTrace)
  (bold_edges : list GraphEdge)
  : string :=
  fold_left append [
    StringOfProcessor processor;
    StringOfPathNames (rev pathmap);
    StringOfTrace trace bold_edges
    ] EmptyString.

(** It is safe to pass an empty list as the [processor] and as the [pathmap] -
the names given in the graphviz output just won't be as helpful.  See above. *)
Definition GraphvizCompressedGraph
  (processor : Processor)
  (pathmap : MicroopPathMap)
  (g : list GraphEdge)
  (trace : GraphGenerationTrace)
  (do_reduction : bool)
  : list string :=
  let g' :=
    if do_reduction
    then EdgesFromAdjacencyList (AdjacencyListTransitiveReduction
        (AdjacencyListFromEdges g))
    else g in
  let bold_edges :=
    match Topsort g' with
    | Cyclic e =>
       match FindCycle e with
       | Some l => l
       | None => []
       end
    | _ => []
    end in
  fold_left (app (A:=_)) [
    ["digraph G {"; newline];
    [tab; "overlap=scale;"; newline];
    [tab; "splines=true;"; newline];
    [tab; "label="; quote; GraphvizTitle processor pathmap trace bold_edges;
      quote; ";"; newline];
    GraphvizEdges g' bold_edges;
    GraphvizNodes processor (NodesFromEdges g');
    ["}"; newline]
  ] [].

Module GraphvizExamples.

Definition dummyProc := mkProcessor "DummyProc" (fun _ => true) [].

Example e1 :
  GraphvizShortStringOfGraphNode (mkMicroop 0 0 0 (Read 1 1), (2, 3))
  = "n0_0_0_Ry_1_at_2_3".
Proof.
  auto.
Qed.

Example e2 :
  GraphvizPrettyStringOfGraphNode (mkMicroop 0 0 0 (Read 1 1), (2, 3))
  = "Inst 0:0:0\nRy:1\n".
Proof.
  auto.
Qed.

Example e3 :
  GraphvizStringOfGraphEdge
    []
    ""
    ((mkMicroop 0 0 0 (Write 1 1), (2, 3)),
     (mkMicroop 1 0 0 (Read  1 1), (2, 3)),
     "myLabel")
    = StringOf [tab; "n0_0_0_Wy_1_at_2_3 -> n1_0_0_Ry_1_at_2_3 [label="; quote; "myLabel"; quote; ";constraint=false;color=purple;fontcolor=purple;];"; newline].
Proof.
auto.
Qed.

Example e4 :
  GraphvizCompressedGraph dummyProc []
    [((mkMicroop 0 0 0 (Write 1 1), (2, 3)),
      (mkMicroop 1 0 0 (Read  1 1), (2, 3)),
      "myLabel")] ((NormalGraph, [mkTraceEntry "a" 1; mkTraceEntry "b" 0])) true
  = ["digraph G {"; newline;
    tab; "overlap=scale;"; newline;
    tab; "splines=true;"; newline;
    tab; "label="; quote; "Processor: DummyProc\n(no pipelines)\nTrace: NormalGraph\nb: 0\na: 1\nnocycle"; quote; ";"; newline;
    StringOf [tab; "n0_0_0_Wy_1_at_2_3 -> n1_0_0_Ry_1_at_2_3 [label="; quote; "myLabel"; quote; ";constraint=false;color=purple;fontcolor=purple;];"; newline];
    StringOf [tab; "n1_0_0_Ry_1_at_2_3 [shape=circle;label="; quote; quote; ";pos="; quote; "2,-3!"; quote; ";];"; newline];
    StringOf [tab; "n0_0_0_Wy_1_at_2_3 [shape=circle;label="; quote; quote; ";pos="; quote; "1,-3!"; quote; ";];"; newline];
    "}"; newline].
Proof.
auto.
Qed.

End GraphvizExamples.

Close Scope string_scope.
