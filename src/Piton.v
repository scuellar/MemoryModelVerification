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
(* DEALINGS IN THE SOFTWARE.                                                   *)
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

Definition CorePipelineStages := [
  (** 0 *) "Fetch";
  (** 1 *) "ThreadSelect";                          
  (** 2 *) "Decode";
  (** 3 *) "Execute";
  (** 4 *) "MemoryStage";
  (** 5 *) "Writeback";
  (** 6 *) "StoreBufferOnly";
  (** 7 *) "LoadMissQueue";
  (** 8 *) "L1 ViCL Create";
  (** 9 *) "L1 ViCL Invalidate";
  (** 10 *) "L1.5 ViCL Create";
  (** 11 *) "L1.5 ViCL Invalidate" ].

Definition LoadMissPipelineStages := [                          
  (** 12 *) "Execute-LM";
  (** 13 *) "MemoryStage-LM";
  (** 14 *) "Writeback-LM"].

Definition PitonPipelineStages:= (CorePipelineStages ++ LoadMissPipelineStages)%list.

Definition PitonPipelineL1ComplPropagations (n : PipeID) :=
  (** ((a, b), (c, d)) means "if there are instructions [i1] and [i2] such that
  there is an edge from (i1 @ a) to (i2 @ b), then add an edge from (i1 @ c) to
  (i2 @ d)" *)
  [(((n, 0), (n, 0)), ((n, 1), (n, 1)));  (* Fetch -> Decode *)
   (((n, 1), (n, 1)), ((n, 2), (n, 2)));  (* Decode -> Execute *)
   (((n, 2), (n, 2)), ((n, 3), (n, 3)));  (* Execute -> Memory *)
   (((n, 3), (n, 3)), ((n, 4), (n, 4)));  (* Memory -> Writeback *)
   (((n, 4), (n, 4)), ((n, 5), (n, 5)));  (* Writeback -> StoreBuffer *)
   (((n, 5), (n, 5)), ((n, 6), (n, 6)));  (* Writeback -> StoreBuffer *)
   (((n, 6), (n, 6)), ((n, 8), (n, 6)));   (* StoreBuffer one at a time to L2 *)
   (((n, 6), (n, 6)), ((n, 10), (n, 6)))   (* StoreBuffer one at a time to L2 *)
  ].

Definition LoadMissPipelineComplPropagations (n : PipeID) :=
  (** ((a, b), (c, d)) means "if there are instructions [i1] and [i2] such that
  there is an edge from (i1 @ a) to (i2 @ b), then add an edge from (i1 @ c) to
  (i2 @ d)" *)
  [ (((n, 0), (n, 0)), ((n, 1), (n, 1)));  (* Fetch -> Decode *)
    (((n, 1), (n, 1)), ((n, 2), (n, 2)));  (* Decode -> Execute *)
    (((n, 2), (n, 2)), ((n, 3), (n, 3)));  (* Execute -> Memory *)
    (((n, 3), (n, 3)), ((n, 4), (n, 4)));  (* Memory -> Writeback *)
    (((n, 4), (n, 4)), ((n, 7), (n, 4)));  (* Writeback -> StoreBuffer *)
    (((n, 7), (n, 4)), ((n, 12), (n, 4)));  (* Writeback -> StoreBuffer *)
    (((n, 12), (n, 4)), ((n, 13), (n, 4)));  (* Writeback -> StoreBuffer *)
    (((n, 13), (n, 4)), ((n, 14), (n, 5)))  (* Writeback -> StoreBuffer *) (*TODO:true?*)
  ].

Definition PitonPerformEdgeInterpretation :=
  mkInterpretation
  (fun e =>
    (** RF: ViCL Create -> ViCL Create at L1 and L2 *)
    [])
  (fun e =>
    (** WS: ViCL Inv -> ViCL Create over the cross product of L1 and L2 *)
    [((fst e, (threadID (fst e), 9)), (snd e, (threadID (snd e), 8)), "WS");
     ((fst e, (threadID (fst e), 11)), (snd e, (threadID (snd e), 8)), "WS");
     ((fst e, (threadID (fst e), 9)), (snd e, (threadID (snd e), 10)), "WS");
     ((fst e, (threadID (fst e), 11)), (snd e, (threadID (snd e), 10)), "WS")
    ])
  (fun e =>
    (** FR: ViCL Invalidate -> ViCL Create over the cross product of L1 and L2 *)
    []).

Definition PitonMicroopPaths
  (n : nat)
  (i : Microop)
  : list MicroopPath :=
  match access i with
  | Read  _ _ => [
     mkMicroopPath "ReadFromStoreBuffer"
         (StraightLine n [0; 1; 2; 3; 4; 5])
         (PitonPipelineL1ComplPropagations n)
         [ReadsBetween WritesOnly (n, 4) (n, 4) (n, 8)]
           PitonPerformEdgeInterpretation;
     mkMicroopPath "CacheHitL1"
         (StraightLine n [0; 1; 2; 3; 4; 5])
         (PitonPipelineL1ComplPropagations n)
         [ReadsBetween AnyAccess (n, 8) (n, 4) (n, 9);
           FlushThread WritesOnly [(n, 8);(n, 10)] (n, 4)] (* STB must be empty *)
         PitonPerformEdgeInterpretation;
     mkMicroopPath "CachePseudoMiss" (*Hit but no ViCL valid*)
         (StraightLine n [0; 1; 2; 3; 4; 5] ++ StraightLine n [8; 4; 9])
         (PitonPipelineL1ComplPropagations n)
         [FlushThread WritesOnly [(n, 8);(n, 10)] (n, 4)] (* STB must be empty *)
           PitonPerformEdgeInterpretation;
     mkMicroopPath "CacheLMQHitL1.5"
         (StraightLine n [0; 1; 2; 3; 4; 7; 12; 13; 14] ++ StraightLine n [8; 13; 9])
         (LoadMissPipelineComplPropagations n)
         [ReadsBetween AnyAccess (n, 10) (n, 4) (n, 11);
           FlushThread WritesOnly [(n, 8);(n, 10)] (n, 4)] (* STB must be empty *)
           PitonPerformEdgeInterpretation;
     mkMicroopPath "CacheLMQPseudoMissL1.5" (*Hit but no ViCL valid*)
         (StraightLine n [0; 1; 2; 3; 4; 7; 12; 13; 14] ++ StraightLine n [10; 8; 13; 9]
         ++ StraightLine n [10; 11])
         (LoadMissPipelineComplPropagations n)
         [FlushThread WritesOnly [(n, 8);(n, 10)] (n, 4)] (* STB must be empty *)
           PitonPerformEdgeInterpretation
    (* ; mkMicroopPath "CacheLMQMissL1.5"
         (StraightLine n [0; 1; 2; 3; 4; 7; 10; 11; 12] ++ StraightLine n [8; 11; 9])
         (LoadMissPipelineComplPropagations n)
         [FlushThread WritesOnly [(n, 8);(n, 10)] (n, 4)] (* STB must be empty *)
           PitonPerformEdgeInterpretation*) (*Makes no difference wihtout memory or L2*)
     ]
 | Write _ _ => [
     mkMicroopPath "WriteL1L2"
       (StraightLine n [0; 1; 2; 3; 4; 5; 6; 8; 9; 10; 11])
       (PitonPipelineL1ComplPropagations n)
       []
       PitonPerformEdgeInterpretation;
     mkMicroopPath "WriteL1.5"                         (*This is the case where write skips L1*)
       (StraightLine n [0; 1; 2; 3; 4; 5; 6; 10; 11])
       (PitonPipelineL1ComplPropagations n)
       []
       PitonPerformEdgeInterpretation 
     ]
 | Fence _   => [
     mkMicroopPath "Fence"
       (StraightLine n [0; 1; 2; 3; 4; 5])
       (PitonPipelineL1ComplPropagations n)
       [FlushThread WritesOnly [(n, 8);(n, 10)] (n, 4)]
       PitonPerformEdgeInterpretation
     ]
 end.

Definition PitonProcessor
  (num_cores : nat)
  : Processor :=
  let p n := mkPipeline "Piton" n [8; 10]
    (PitonMicroopPaths n) PitonPipelineStages in
  mkProcessor "PitonProcessor" (map p (Range num_cores)).

