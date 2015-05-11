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
  (processor : Processor)
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
          "\n@Pipe ";
          stringOfNat p;
          ", ";
          StageName processor node
      ]
  end.

Definition GraphvizStringOfGraphNode
  (processor : Processor)
  (props : string)
  (n : GraphNode)
  : string :=
  StringOf [tab; GraphvizShortStringOfGraphNode n; " [label="; quote;
    GraphvizPrettyStringOfGraphNode processor n; quote; ";";
    "pos="; quote; stringOfNat (globalID (fst n)); ",-"; stringOfNat (snd (snd n)); "!"; quote; ";";
    props; "];";
    newline].

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
    let thickness :=
      if existsb (beq_edge e) bold
      then "penwidth=10;color=red;"
      else EmptyString
    in
    StringOf [
      tab; GraphvizShortStringOfGraphNode s; " -> ";
      GraphvizShortStringOfGraphNode d; " [label="; quote; label; quote; ";";
      constraint; thickness; props; "];"; newline]
  end.

Definition GraphvizEdges
  (l : list GraphEdge)
  (bold : list GraphEdge)
  : list string :=
  map (GraphvizStringOfGraphEdge bold "") l.

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

Definition GraphvizNodes
  (processor : Processor)
  (l : list GraphNode)
  : list string :=
  Map (GraphvizStringOfGraphNode processor EmptyString) l.

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
  | [] => EmptyString
  end.

Definition GraphvizTitle
  (processor : Processor)
  (pathmap : MicroopPathMap)
  : string :=
  append (StringOfProcessor processor) (StringOfPathNames (rev pathmap)).

(** It is safe to pass an empty list as the [processor] and as the [pathmap] -
the names given in the graphviz output just won't be as helpful.  See above. *)
Definition GraphvizGraph
  (processor : Processor)
  (pathmap : MicroopPathMap)
  (g : list GraphEdge)
  : list string :=
  let g' := EdgesFromAdjacencyList (AdjacencyListTransitiveReduction
    (AdjacencyListFromEdges g)) in
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
    [tab; "label="; quote; GraphvizTitle processor pathmap; quote; ";"; newline];
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
  GraphvizPrettyStringOfGraphNode dummyProc (mkMicroop 0 0 0 (Read 1 1), (2, 3))
  = "Inst 0:0:0\nRy:1\n@Pipe 2, Loc 3".
Proof.
  auto.
Qed.

Example e3 :
  GraphvizStringOfGraphEdge
    []
    "color=blue"
    ((mkMicroop 0 0 0 (Write 1 1), (2, 3)),
     (mkMicroop 1 0 0 (Read  1 1), (2, 3)),
     "myLabel")
    = StringOf [tab; "n0_0_0_Wy_1_at_2_3 -> n1_0_0_Ry_1_at_2_3 [label="; quote;
    "myLabel"; quote; ";constraint=false;color=blue];"; newline].
Proof.
auto.
Qed.

Example e4 :
  GraphvizGraph dummyProc []
    [((mkMicroop 0 0 0 (Write 1 1), (2, 3)),
      (mkMicroop 1 0 0 (Read  1 1), (2, 3)),
      "myLabel")]
  = ["digraph G {"; newline;
    tab; "overlap=scale;"; newline;
    tab; "splines=true;"; newline;
    tab; "label="; quote; "Processor: DummyProc\n(no pipelines)"; quote; ";"; newline;
    StringOf [tab; "n0_0_0_Wy_1_at_2_3 -> n1_0_0_Ry_1_at_2_3 [label="; quote; "myLabel"; quote; ";constraint=false;];"; newline];
    StringOf [tab; "n1_0_0_Ry_1_at_2_3 [label="; quote; "Inst 1:0:0\nRy:1\n@Pipe 2, Loc 3"; quote; ";pos="; quote; "1,-3!"; quote; ";];"; newline];
    StringOf [tab; "n0_0_0_Wy_1_at_2_3 [label="; quote; "Inst 0:0:0\nWy:1\n@Pipe 2, Loc 3"; quote; ";pos="; quote; "0,-3!"; quote; ";];"; newline];
    "}"; newline].
Proof.
auto.
Qed.

End GraphvizExamples.

Close Scope string_scope.
