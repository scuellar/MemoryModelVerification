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
Require Import Util.
Require Import Instruction.
Require Import Processor.

Import ListNotations.
Open Scope string_scope.

(** * Five Stage Pipeline with no ViCLs *)

(** Each core has a five-stage, in-order pipeline and a store buffer, and all
cores share a memory hierarchy.  It is designed to be a relatively simple
example of a pipeline which implements TSO. *)

(** ** Stages/Locations *)

(** Each individual processor core is defined in terms of a list of pipeline
stages.  Here, we name the stages one by one. *)

Definition FiveStageLAB4PipelineStages := [
  (* 0 *) "Fetch";
  (* 1 *) "Decode";
  (* 2 *) "Mul0";
  (* 3 *) "Mul1";
  (* 4 *) "Mul2";
  (* 5 *) "Mul3";
  (* 6 *) "Mem0";
  (* 7 *) "Mem1";
  (* 8 *) "Mem2";
  (* 9 *) "Mem3";
  (* 10 *) "ALU0";
  (* 11 *) "ALU0";
  (* 12 *) "ALU0";
  (* 13 *) "ALU0";
  (* 14 *) "Commit"].

(** Each node in the PipeCheck uhb graph is defined by a triple of three
numbers: the associated [Microop], a [PipeID], and a stage ID.  The pairing of
[PipeID] and stage ID is called a [Location].  For example, for a core with
[PipeID] [n], the location <<(n, 2)>> would be the Execute stage of that core,
and the uhb [GraphNode] <<(uop, (n, 2))>> represents [Microop] <<uop>> passing
through location <<(n, 2)>>. *)

(** ** Propagated (Intra-Location) Edges *)

Definition FiveStageLAB4PipelinePropagations (n : PipeID) :=
  (** Let <<a>>, <<b>>, <<c>>, and <<d>> be [Location]s from the list above.
  ((a, b), (c, d)) here means "if there are [Microop]s [i1] and [i2] such that
  there is an edge from (i1 @ a) to (i2 @ b), then add an edge from (i1 @ c) to
  (i2 @ d)".  This represents per-stage local ordering guarantees. *)
  [
  (** Decode is FIFO: Propagate edges from Fetch -> Decode *)
  (((n, 0), (n, 0)), ((n, 1), (n, 1)));
  (** X0 **)
  (((n, 1), (n, 1)), ((n, 2), (n, 2)));
  (((n, 1), (n, 1)), ((n, 6), (n, 6)));
  (((n, 1), (n, 1)), ((n, 10), (n, 10)));
  (** MUL **)
  (((n, 2), (n, 2)), ((n, 3), (n, 3)));
  (((n, 3), (n, 3)), ((n, 4), (n, 4)));
  (((n, 4), (n, 4)), ((n, 5), (n, 5)));
  (** MEM **)
  (((n, 6), (n, 6)), ((n, 7), (n, 7)));
  (((n, 7), (n, 7)), ((n, 8), (n, 8)));
  (((n, 8), (n, 8)), ((n, 9), (n, 9)));
  (** ALU **)
  (((n, 10), (n, 10)), ((n, 11), (n, 11)));
  (((n, 11), (n, 11)), ((n, 12), (n, 12)));
  (((n, 12), (n, 12)), ((n, 13), (n, 13)));
  (** Commit *)
  (((n, 0), (n, 0)), ((n, 14), (n, 14)))
  
  ].

(** ** Performing Locations *)

(** This is the most confusing part of the pipeline definition syntax, and it
is likely to change... *)

(** PipeCheck automatically calculates the set of RF, WS, and FR edges for a
given litmus test.  However, the pipeline definition has to tell PipeCheck how
to interpret these edges in a microarchitectural sense.  This currently works
as follows.

Performing edges are defined via a triple of three functions representing RF,
WS, and FR, respectively.  Each takes in a pair of [Microop]s representing the
source and destination of the hb edge.  Each returns a pair of uhb nodes
representing the source and destination, respectively, of uhb edges of the
relevant type (RF, WS, or FR).  The uhb edge that is generated gets its source
uhb node from the performing edge location definition of the source [Microop],
and it gets its destination uhb node from the performing edge location
definition of the target [Microop].
*)

Definition FiveStageLAB4PipelinePerformEdgeInterpretation :=
  (** For [Microop]s that access memory *)
  mkInterpretation
    (** RF edges go from the Memory stage of the source write to the
    Execution Stage of the target read. *)
  (fun uop_pair =>
    [Some ((fst uop_pair, (threadID (fst uop_pair), 7)),
           (snd uop_pair, (threadID (snd uop_pair), 6)), "RF")])
    (** WS edges go from the MemoryHierarchy stage of the source write to the
    MemoryHierarchy stage of the target write. *)
  (fun uop_pair =>
    [((fst uop_pair, (threadID (fst uop_pair), 6)),
      (snd uop_pair, (threadID (snd uop_pair), 6)), "WS")])
    (** FR edges go from the MemoryStage of the source read to the
    MemoryHierarchy stage of the target write. *)
  (fun uop_pair =>
    [((fst uop_pair, (threadID (fst uop_pair), 6)),
      (snd uop_pair, (threadID (snd uop_pair), 7)), "FR")]).

Definition FiveStageLAB4PipelineSTBPerformEdgeInterpretation :=
  (** Read [Microop]s that don't access memory don't use performing edges *)
  mkInterpretation
  (fun e => []) (fun e => []) (fun e => []).

(** ** Paths per Microop *)

(** A [MicroopPath] definition has 5 components:
- a descriptive name
- the actual path through the pipeline, where the numbers refer to the list
  of stage names defined at the top
- a list of propagated edges, representing local reordering guarantees (see
  above)
- a list of extra constraints (if any) that must be satisfied for instructions
  taking that path
- a definition of how to interpret performing edges (RF, WS, and FR) (see above)

The only component not yet mentioned is the set of [ExtraConstraint]s.  There
are currently two choices:
- <<[ReadsBetween] n f a b c>> says that if [Microop] <<i1>> takes this path,
  there must be another Microop <<i2>> such that there are uhb edges
  <<(i2 @ a) --> (i1 @ b) --> (i2 @ c)>> with the name n, and such that <<a>>,
  <<b>>, and <<c>> satisfy <<f b a>>.
- <<[FlushThread] n f a b>> says that if [Microop] <<i1>> takes this path,
  there must be another Microop <<i2>> such that there are uhb edges
  <<(i2 @ a) --> (i1 @ b)>> with the name n, and such that <<a>> and <<b>>
  satisfy <<f b a>>. Do you mean f (i2 @ a) (i1 @ b)?
*)

Definition FiveStageLAB4PipelineMicroopPaths
  (n : nat)
  (i : Microop)
  : list MicroopPath :=
  match access i with
  | Read  _ _ => [
     mkMicroopPath "ReadFromMemory"
         (StraightLine n [0; 1; 7; 8; 9; 14])
         (FiveStageLAB4PipelinePropagations n)
         [] (*TODO: used to be: FlushThread "STBEmpty" RAWSameAddress (n, 7) (n, 6)*)
         FiveStageLAB4PipelinePerformEdgeInterpretation
     ]
 | Write _ _ => [
     mkMicroopPath "Write"
       (StraightLine n [0; 1; 7; 8; 9; 14])
         (FiveStageLAB4PipelinePropagations n)
       []

       FiveStageLAB4PipelinePerformEdgeInterpretation
     ]
 | Fence _  => []
  end.

(** ** Putting it all together *)

(** Create a processor with <n> identical cores of the type defined above. *)

Definition FiveStageLAB4Processor
  (num_cores : nat)
  : Processor :=
  let p n := mkPipeline "FiveStageLAB4Pipeline" n []
    (FiveStageLAB4PipelineMicroopPaths n)
    FiveStageLAB4PipelineStages in
  mkProcessor "FiveStageLAB4Processor" (map p (Range num_cores)).
