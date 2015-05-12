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

Definition PitonPipelineStages := [
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
  (** 11 *) "L1.5 ViCL Invalidate";
  (** 12 *) "L2 ViCL Create";
  (** 13 *) "L2 ViCL Invalidate" ].

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
   (((n, 6), (n, 6)), ((n, 8), (n, 6)))   (* StoreBuffer one at a time to L1 *)
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

Definition PitonPerformEdgeInterpretation :=
  mkInterpretation
  (fun e =>
    (** RF: ViCL Create -> ViCL Create at L1 and L2 *)
    [])
  (fun e =>
    (** WS: ViCL Inv -> ViCL Create over the cross product of L1 and L2 *)
    [((fst e, (threadID (fst e), 9)), (snd e, (threadID (snd e), 8)), "WS");
     ((fst e, (threadID (fst e), 11)), (snd e, (threadID (snd e), 8)), "WS");
     ((fst e, (threadID (fst e), 13)), (snd e, (threadID (snd e), 8)), "WS");
     ((fst e, (threadID (fst e), 9)), (snd e, (threadID (snd e), 10)), "WS");
     ((fst e, (threadID (fst e), 11)), (snd e, (threadID (snd e), 10)), "WS");
     ((fst e, (threadID (fst e), 13)), (snd e, (threadID (snd e), 10)), "WS");
     ((fst e, (threadID (fst e), 9)), (snd e, (threadID (snd e), 12)), "WS");
     ((fst e, (threadID (fst e), 11)), (snd e, (threadID (snd e), 12)), "WS");
     ((fst e, (threadID (fst e), 13)), (snd e, (threadID (snd e), 12)), "WS")
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
     mkMicroopPath "ReadFromL1StoreBuffer"
         (StraightLine n [0; 1; 2; 3; 4; 5])
         (PitonPipelineL1ComplPropagations n)
         [ReadsBetween WritesOnly (n, 4) (n, 4) (n, 8)]
           PitonPerformEdgeInterpretation;
     mkMicroopPath "CacheHitL1"
         (StraightLine n [0; 1; 2; 3; 4; 5])
         (PitonPipelineL1ComplPropagations n)
         [ReadsBetween AnyAccess (n, 8) (n, 4) (n, 9);
           FlushThread WritesOnly [(n, 8); (n, 10); (n,16)] (n, 4)] (* STB must be empty *)
         PitonPerformEdgeInterpretation;
     mkMicroopPath "CacheLMQHitL1.5"
         (StraightLine n [0; 1; 2; 3; 4; 7; 5] ++ StraightLine n [8; 7; 9])
         (LoadMissPipelineComplPropagations n)
         [ReadsBetween AnyAccess (n, 10) (n, 7) (n, 11);
           FlushThread WritesOnly [(n, 8);(n, 10); (n,16)] (n, 4)] (* STB must be empty *)
           PitonPerformEdgeInterpretation;
     mkMicroopPath "CacheLMQMissL1.5HitL2"
         (StraightLine n [0; 1; 2; 3; 4; 7; 5] 
          ++ StraightLine n [10; 8; 7; 9] ++ StraightLine n [10; 7; 11] )
         (LoadMissPipelineComplPropagations n)
         [ReadsBetween AnyAccess (n, 12) (n, 7) (n, 13);
           FlushThread WritesOnly [(n, 8);(n, 10); (n,16)] (n, 4)] (* STB must be empty *)
         PitonPerformEdgeInterpretation;
     mkMicroopPath "CacheLMQMissL1.5MissL2"
         (StraightLine n [0; 1; 2; 3; 4; 7; 5] 
          ++ StraightLine n [12; 10; 8; 7; 9] ++ StraightLine n [12; 10; 7; 11]
          ++ StraightLine n [12; 7; 13])
         (LoadMissPipelineComplPropagations n)
         [FlushThread WritesOnly [(n, 8);(n, 10); (n,16)] (n, 4)] (* STB must be empty *)
         PitonPerformEdgeInterpretation
     ]
 | Write _ _ => [
     mkMicroopPath "WriteL1L2"
       (*The order corresponds to write-through 
         10 -> 8 and writh-back 11 -> 12*)
       (StraightLine n [0; 1; 2; 3; 4; 5; 6; 10; 8; 9; 11; 12; 13] )
       (PitonPipelineL1ComplPropagations n)
       []
       PitonPerformEdgeInterpretation
     ]
 | Fence _   => [
     mkMicroopPath "Fence"
       (StraightLine n [0; 1; 2; 3; 4; 5])
       (PitonPipelineL1ComplPropagations n)
       [ FlushThread WritesOnly [(n, 8)] (n, 4);
         FlushThread WritesOnly [(n, 10)] (n, 4);
         FlushThread WritesOnly [(n, 12)] (n, 4)]
       PitonPerformEdgeInterpretation
     ]
 end.


Definition LastViCL:= 12.
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

Definition PitonProcessor
  (num_cores : nat)
  : Processor :=
  let p n := mkPipeline "Piton" n [10; 12] (*[8; 10]*)
    (PitonMicroopPaths n) PitonPipelineStages in
  mkProcessor "PitonProcessor" SourcingConstraints (map p (Range num_cores)).
