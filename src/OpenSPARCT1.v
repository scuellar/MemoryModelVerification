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
Require Import Arith.
Require Import String.
Require Import Util.
Require Import Instruction.
Require Import Processor.
Require Import Graph.

Import ListNotations.
Open Scope string_scope.

(** * Pipeline Definition Example *)
(** This is a two-core processor.  Each core has a five-stage, in-order
pipeline, a store buffer, and a private L1 cache (split into "ValueInCacheLine
Create" and "ValueInCacheLine Invalidate" events).  It is designed to be a
relatively simple example of a pipeline which implements TSO. *)

Definition OpenSPARCT1PipelineStages := [
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
  (** 10 *) "L2 ViCL Create";
  (** 11 *) "L2 ViCL Invalidate" ].

Definition OpenSPARCT1PipelineComplPropagations (n : PipeID) :=
  (** ((a, b), (c, d)) means "if there are instructions [i1] and [i2] such that
  there is an edge from (i1 @ a) to (i2 @ b), then add an edge from (i1 @ c) to
  (i2 @ d)" *)
  [(((n, 0), (n, 0)), ((n, 1), (n, 1)));  (* Fetch -> Decode *)
   (((n, 1), (n, 1)), ((n, 2), (n, 2)));  (* Decode -> Execute *)
   (((n, 2), (n, 2)), ((n, 3), (n, 3)));  (* Execute -> Memory *)
   (((n, 3), (n, 3)), ((n, 4), (n, 4)));  (* Memory -> Writeback *)
   (((n, 4), (n, 4)), ((n, 5), (n, 5)));  (* Writeback -> StoreBuffer *)
   (((n, 5), (n, 5)), ((n, 6), (n, 6)));  (* Writeback -> StoreBuffer *)
   (((n, 6), (n, 6)), ((n, 8), (n, 6)));  (* StoreBuffer one at a time to L2 *)
   (((n, 6), (n, 6)), ((n, 10), (n, 6)))  (* StoreBuffer one at a time to L2 *)
  ].

Definition LoadMissPipelineComplPropagations (n : PipeID) :=
  (** ((a, b), (c, d)) means "if there are instructions [i1] and [i2] such that
  there is an edge from (i1 @ a) to (i2 @ b), then add an edge from (i1 @ c) to
  (i2 @ d)" *)
  [(((n, 0), (n, 0)), ((n, 1), (n, 1)));  (* Fetch -> Decode *)
   (((n, 1), (n, 1)), ((n, 2), (n, 2)));  (* Decode -> Execute *)
   (((n, 2), (n, 2)), ((n, 3), (n, 3)));  (* Execute -> Memory *)
   (((n, 3), (n, 3)), ((n, 4), (n, 4)));  (* Memory -> Writeback *)
   (((n, 4), (n, 4)), ((n, 7), (n, 4)));  (* Writeback -> StoreBuffer *)
   (((n, 7), (n, 4)), ((n, 5), (n, 5)))  (* Writeback -> StoreBuffer *)
  ].

Definition OpenSPARCT1PerformEdgeInterpretation :=
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

Definition OpenSPARCT1MicroopPaths
  (n : nat)
  (i : Microop)
  : list MicroopPath :=
  match access i with
  | Read  _ _ => [
     mkMicroopPath "ReadFromStoreBuffer"
         (StraightLine n [0; 1; 2; 3; 4; 5])
         (OpenSPARCT1PipelineComplPropagations n)
         [ReadsBetween WritesOnly (n, 4) (n, 4) (n, 8)]
           OpenSPARCT1PerformEdgeInterpretation;
     mkMicroopPath "CacheHitL1"
         (StraightLine n [0; 1; 2; 3; 4; 5])
         (OpenSPARCT1PipelineComplPropagations n)
         [ReadsBetween AnyAccess (n, 8) (n, 4) (n, 9);
           FlushThread WritesOnly [(n, 8); (n, 10)] (n, 4)] (* STB must be empty *)
         OpenSPARCT1PerformEdgeInterpretation;
     mkMicroopPath "CacheMissLMQHitL2"
         (StraightLine n [0; 1; 2; 3; 4; 7; 5]
          ++ StraightLine n [8; 7; 9] )
         (LoadMissPipelineComplPropagations n)
         [ReadsBetween AnyAccess (n, 10) (n, 7) (n, 11);
           FlushThread WritesOnly [(n, 8); (n, 10)] (n, 4)] (* STB must be empty *)
           OpenSPARCT1PerformEdgeInterpretation;
     mkMicroopPath "CacheMissLMQMissL2"
         (StraightLine n [0; 1; 2; 3; 4; 7; 5]
          ++ StraightLine n [10; 8; 7; 9] ++ StraightLine n [10; 7; 11] )
         (LoadMissPipelineComplPropagations n)
         [FlushThread WritesOnly [(n, 8); (n, 10)] (n, 4)] (* STB must be empty *)
           OpenSPARCT1PerformEdgeInterpretation
     ]
 | Write _ _ => [
     mkMicroopPath "WriteL1L2"
       (StraightLine n [0; 1; 2; 3; 4; 5; 6; 8; 9; 10; 11])
       (OpenSPARCT1PipelineComplPropagations n)
       []
       OpenSPARCT1PerformEdgeInterpretation
     ]
 | Fence _   => [
     mkMicroopPath "Fence"
       (StraightLine n [0; 1; 2; 3; 4; 5])
       (OpenSPARCT1PipelineComplPropagations n)
       [FlushThread WritesOnly [(n, 8);(n, 10)] (n, 4)]
       OpenSPARCT1PerformEdgeInterpretation
     ]
 end.

Definition LastViCL:= 10.
Definition SourcingConstraints
  (sourcing : (option (GraphNode * GraphNode) * (GraphNode * GraphNode)))
  : bool :=
  let (n1op, n2) := sourcing in
  match n1op with
  | None => true (* Don't remove cases where a ViCL is sourced from the
                  initial state *)
  | Some n1 =>
      let (c1, i1) := n1 in
      let (c2, i2) := n2 in
      let (uop1, l1) := c1 in
      let (uop2, l2) := c2 in
      let id1 := threadID uop1 in
      let id2 := threadID uop2 in
      let (l1a, l1b) := l1 in
      let (l2a, l2b) := l2 in
      match beq_nat id1 id2 with
      | true =>
        (* Filter based on rules for ops on the same core *)
        (* Is the ViCL source one level below the ViCL being sourced? *)
          orb ( beq_nat (l1b - l2b) 2)
        (* Is this the lowest ViCL level? If so, let it slide by abstraction. *)
          (andb (beq_nat l1b l2b) (beq_nat l1b LastViCL))
        (* Otherwise this isn't a valid case. *)
         
      | false => 
        (* Filter based on rules for ops on different cores *)
        (* Is the ViCL source at the same level as the ViCL being sourced? *)
          (andb (beq_nat l2b LastViCL) (beq_nat l1b LastViCL))
     end
  end.


Definition OpenSPARCT1Processor
  (num_cores : nat)
  : Processor :=
  let p n := mkPipeline "OpenSPARCT1" n [8;10]
    (OpenSPARCT1MicroopPaths n) OpenSPARCT1PipelineStages in
  mkProcessor "OpenSPARCT1Processor" SourcingConstraints (map p (Range num_cores)).

