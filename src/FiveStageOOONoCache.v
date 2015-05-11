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

(** * Pipeline Definition Example *)
(** This is a two-core processor.  Each core has a five-stage, in-order
pipeline, a store buffer, and a private L1 cache (split into "ValueInCacheLine
Create" and "ValueInCacheLine Invalidate" events).  It is designed to be a
relatively simple example of a pipeline which implements TSO. *)

Definition SimpleFiveStagePipelineStages := [
  (** 0 *) "Fetch";
  (** 1 *) "Decode";
  (** 2 *) "Execute";
  (** 3 *) "MemoryStage";
  (** 4 *) "Writeback";
  (** 5 *) "StoreBufferOnly";
  (** 6 *) "MemoryHierarchy";
  (** 7 *) "Issue";
  (** 8 *) "Commit"].

Definition SimpleFiveStagePipelinePropagations (n : PipeID) :=
  (** ((a, b), (c, d)) means "if there are instructions [i1] and [i2] such that
  there is an edge from (i1 @ a) to (i2 @ b), then add an edge from (i1 @ c) to
  (i2 @ d)" *)
  [(((n, 0), (n, 0)), ((n, 1), (n, 1)));  (* Fetch -> Decode *)
   (((n, 1), (n, 1)), ((n, 7), (n, 7)));  (* Decode -> Issue *)
   (((n, 2), (n, 2)), ((n, 3), (n, 3)));  (* Execute -> Memory *)
   (((n, 3), (n, 3)), ((n, 4), (n, 4)));  (* Memory -> Writeback *)
   (((n, 4), (n, 4)), ((n, 5), (n, 5)));  (* Writeback -> StoreBuffer *)
   (((n, 5), (n, 5)), ((n, 6), (n, 5)));  (* StoreBuffer one at a time to L1 *)
   (((n, 0), (n, 0)), ((n, 8), (n, 8)));  (* Commit in order *)
   (((n, 1), (n, 1)), ((n, 3), (n, 3)))   (* Fetch -> Memory; in order memory ops *)
  ].

Definition SimpleFiveStagePipelineSTBPerformEdgeInterpretation :=
  mkInterpretation
  (fun e => []) (fun e => []) (fun e => []).

Definition SimpleFiveStagePipelinePerformEdgeInterpretation :=
  mkInterpretation
  (fun e =>
    [Some ((fst e, (threadID (fst e), 6)), (snd e, (threadID (snd e), 4)), "RF")])
  (fun e =>
    [((fst e, (threadID (fst e), 6)), (snd e, (threadID (snd e), 6)), "WS")])
  (fun e =>
    [((fst e, (threadID (fst e), 4)), (snd e, (threadID (snd e), 6)), "FR")]).

Definition SimpleFiveStagePipelineMicroopPaths
  (n : nat)
  (i : Microop)
  : list MicroopPath :=
  match access i with
  | Read  _ _ => [
     mkMicroopPath "ReadFromStoreBuffer"
         (StraightLine n [0; 1; 7; 2; 3; 4; 8])
         (SimpleFiveStagePipelinePropagations n)
         [ReadsBetween WritesOnly (n, 3) (n, 3) (n, 6)]
         SimpleFiveStagePipelineSTBPerformEdgeInterpretation;
     mkMicroopPath "ReadFromMemory"
         (StraightLine n [0; 1; 7; 2; 3; 4; 8])
         (SimpleFiveStagePipelinePropagations n)
         []
         SimpleFiveStagePipelinePerformEdgeInterpretation
     ]
 | Write _ _ => [
     mkMicroopPath "Write"
       (StraightLine n [0; 1; 7; 2; 3; 4; 8; 5; 6])
         (SimpleFiveStagePipelinePropagations n)
       []
       SimpleFiveStagePipelinePerformEdgeInterpretation
     ]
 | Fence _   => [
     mkMicroopPath "Fence"
       (StraightLine n [0; 1; 7; 2; 3; 4; 8])
         (SimpleFiveStagePipelinePropagations n)
       [FlushThread WritesOnly [(n, 6)] (n, 2)]
       SimpleFiveStagePipelinePerformEdgeInterpretation
     ]
 end.

Definition FiveStageOOONoCacheProcessor
  (num_cores : nat)
  : Processor :=
  let p n := mkPipeline "SimpleFiveStagePipeline" n []
    (SimpleFiveStagePipelineMicroopPaths n)
    SimpleFiveStagePipelineStages in 
  mkProcessor "FiveStageOOONoCacheProcessor" (fun _ => true) (map p (Range num_cores)).
