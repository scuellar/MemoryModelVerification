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

Definition FiveStagePipelineStages := [
  (** 0 *) "Fetch";
  (** 1 *) "Decode";
  (** 2 *) "Execute0";
  (** 3 *) "MemoryStage0";
  (** 4 *) "Writeback0";
  (** 5 *) "StoreBufferOnly";
  (** 6 *) "L1 ViCL Create";
  (** 7 *) "L1 ViCL Invalidate";
  (** 8 *) "L2 ViCL Create";
  (** 9 *) "L2 ViCL Invalidate";
  (** 10 *) "Execute1";
  (** 11 *) "MemoryStage1";
  (** 12 *) "Writeback1"].

Definition FiveStagePipelineL1ComplPropagations_pipe0 (n : PipeID) :=
  (** ((a, b), (c, d)) means "if there are instructions [i1] and [i2] such that
  there is an edge from (i1 @ a) to (i2 @ b), then add an edge from (i1 @ c) to
  (i2 @ d)" *)
  [(((n, 0), (n, 0)), ((n, 1), (n, 1)));  (* Fetch -> Decode *)
   (((n, 1), (n, 1)), ((n, 2), (n, 2)));  (* Decode -> Execute *)
   (((n, 2), (n, 2)), ((n, 3), (n, 3)));  (* Execute -> Memory *)
   (((n, 3), (n, 3)), ((n, 4), (n, 4)));  (* Memory -> Writeback *)
   (((n, 4), (n, 4)), ((n, 5), (n, 5)));  (* Writeback -> StoreBuffer *)
   (((n, 1), (n, 1)), ((n, 2), (n, 10)));
   (((n, 10), (n, 2)), ((n, 11), (n, 3))); (* keep mem ops in order between lanes *)
   (((n, 11), (n, 3)), ((n, 12), (n, 4)));
   (((n, 12), (n, 4)), ((n, 5), (n, 5)));
   (((n, 2), (n, 10)), ((n, 3), (n, 11)));
   (((n, 3), (n, 11)), ((n, 4), (n, 12)));
   (((n, 4), (n, 12)), ((n, 5), (n, 5)));
   (((n, 5), (n, 5)), ((n, 6), (n, 5))) (* StoreBuffer one at a time to L1 *)
  ].

Definition FiveStagePipelineL1ComplPropagations_pipe1 (n : PipeID) :=
  (** ((a, b), (c, d)) means "if there are instructions [i1] and [i2] such that
  there is an edge from (i1 @ a) to (i2 @ b), then add an edge from (i1 @ c) to
  (i2 @ d)" *)
  [(((n, 0), (n, 0)), ((n, 1), (n, 1)));  (* Fetch -> Decode *)
   (((n, 1), (n, 1)), ((n, 10), (n, 10)));  (* Decode -> Execute1 *)
   (((n, 10), (n, 10)), ((n, 11), (n, 11)));  (* Execute1 -> Memory1 *)
   (((n, 11), (n, 11)), ((n, 12), (n, 12)));  (* Memory1 -> Writeback1 *)
   (((n, 12), (n, 12)), ((n, 5), (n, 5)));  (* Writeback1 -> StoreBuffer *)
   (((n, 1), (n, 1)), ((n, 10), (n, 2)));
   (((n, 10), (n, 2)), ((n, 11), (n, 3))); (* keep mem ops in order between lanes *)
   (((n, 11), (n, 3)), ((n, 12), (n, 4)));
   (((n, 12), (n, 4)), ((n, 5), (n, 5)));
   (((n, 2), (n, 10)), ((n, 3), (n, 11)));
   (((n, 3), (n, 11)), ((n, 4), (n, 12)));
   (((n, 4), (n, 12)), ((n, 5), (n, 5)));
   (((n, 5), (n, 5)), ((n, 6), (n, 5)))   (* StoreBuffer one at a time to L1 *)
  ].

Definition FiveStagePipelineL2ComplPropagations_pipe0 (n : PipeID) :=
  (** ((a, b), (c, d)) means "if there are instructions [i1] and [i2] such that
  there is an edge from (i1 @ a) to (i2 @ b), then add an edge from (i1 @ c) to
  (i2 @ d)" *)
  [(((n, 0), (n, 0)), ((n, 1), (n, 1)));  (* Fetch -> Decode *)
   (((n, 1), (n, 1)), ((n, 2), (n, 2)));  (* Decode -> Execute *)
   (((n, 2), (n, 2)), ((n, 3), (n, 3)));  (* Execute -> Memory *)
   (((n, 3), (n, 3)), ((n, 4), (n, 4)));  (* Memory -> Writeback *)
   (((n, 4), (n, 4)), ((n, 5), (n, 5)));  (* Writeback -> StoreBuffer *)
   (((n, 1), (n, 1)), ((n, 2), (n, 10)));
   (((n, 10), (n, 2)), ((n, 11), (n, 3))); (* keep mem ops in order between lanes *)
   (((n, 11), (n, 3)), ((n, 12), (n, 4)));
   (((n, 12), (n, 4)), ((n, 5), (n, 5)));
   (((n, 2), (n, 10)), ((n, 3), (n, 11)));
   (((n, 3), (n, 11)), ((n, 4), (n, 12)));
   (((n, 4), (n, 12)), ((n, 5), (n, 5)));
   (((n, 5), (n, 5)), ((n, 8), (n, 5)))   (* StoreBuffer one at a time to L2 *)
  ].                                      (* (necessary if writing directly to L2) *)

Definition FiveStagePipelineL2ComplPropagations_pipe1 (n : PipeID) :=
  (** ((a, b), (c, d)) means "if there are instructions [i1] and [i2] such that
  there is an edge from (i1 @ a) to (i2 @ b), then add an edge from (i1 @ c) to
  (i2 @ d)" *)
  [(((n, 0), (n, 0)), ((n, 1), (n, 1)));      (* Fetch -> Decode *)
   (((n, 1), (n, 1)), ((n, 10), (n, 10)));    (* Decode -> Execute1 *)
   (((n, 10), (n, 10)), ((n, 11), (n, 11)));  (* Execute1 -> Memory1 *)
   (((n, 11), (n, 11)), ((n, 12), (n, 12)));  (* Memory1 -> Writeback1 *)
   (((n, 12), (n, 12)), ((n, 5), (n, 5)));    (* Writeback1 -> StoreBuffer *)
   (((n, 1), (n, 1)), ((n, 10), (n, 2)));
   (((n, 10), (n, 2)), ((n, 11), (n, 3))); (* keep mem ops in order between lanes *)
   (((n, 11), (n, 3)), ((n, 12), (n, 4)));
   (((n, 12), (n, 4)), ((n, 5), (n, 5)));
   (((n, 2), (n, 10)), ((n, 3), (n, 11)));
   (((n, 3), (n, 11)), ((n, 4), (n, 12)));
   (((n, 4), (n, 12)), ((n, 5), (n, 5)));
   (((n, 5), (n, 5)), ((n, 8), (n, 5)))       (* StoreBuffer one at a time to L1 *)
  ].                                   (* (necessary if writing directly to L2) *)

Definition FiveStagePipelinePerformEdgeInterpretation :=
  mkInterpretation
  (fun e =>
    (** RF: ViCL Create -> ViCL Create at L1 and L2 *)
    [Some ((fst e, (threadID (fst e), 6)), (snd e, (threadID (snd e), 6)), "RF");
     Some ((fst e, (threadID (fst e), 8)), (snd e, (threadID (snd e), 6)), "RF_Local");
     Some ((fst e, (threadID (fst e), 8)), (snd e, (threadID (snd e), 8)), "RF")
    ])
  (fun e =>
    (** WS: ViCL Inv -> ViCL Create over the cross product of L1 and L2 *)
    [((fst e, (threadID (fst e), 7)), (snd e, (threadID (snd e), 6)), "WS");
     ((fst e, (threadID (fst e), 9)), (snd e, (threadID (snd e), 6)), "WS");
     ((fst e, (threadID (fst e), 7)), (snd e, (threadID (snd e), 8)), "WS");
     ((fst e, (threadID (fst e), 9)), (snd e, (threadID (snd e), 8)), "WS")
    ])
  (fun e =>
    (** FR: ViCL Invalidate -> ViCL Create over the cross product of L1 and L2 *)
    [((fst e, (threadID (fst e), 7)), (snd e, (threadID (snd e), 6)), "FR");
     ((fst e, (threadID (fst e), 9)), (snd e, (threadID (snd e), 6)), "FR");
     ((fst e, (threadID (fst e), 7)), (snd e, (threadID (snd e), 8)), "FR");
     ((fst e, (threadID (fst e), 9)), (snd e, (threadID (snd e), 8)), "FR")
    ]).

Definition FiveStagePipelineMicroopPaths
  (n : nat)
  (i : Microop)
  : list MicroopPath :=
  match access i with
  | Read  _ _ => [
     mkMicroopPath "ReadFromStoreBuffer_pipe0"
         (StraightLine n [0; 1; 2; 3; 4])
         (FiveStagePipelineL1ComplPropagations_pipe0 n)
         [ReadsBetween WritesOnly (n, 3) (n, 3) (n, 6)]
           FiveStagePipelinePerformEdgeInterpretation;
     mkMicroopPath "CacheHitL1_pipe0"
         (StraightLine n [0; 1; 2; 3; 4])
         (FiveStagePipelineL1ComplPropagations_pipe0 n)
         [ReadsBetween AnyAccess (n, 6) (n, 3) (n, 7);
           FlushThread WritesOnly [(n, 6); (n, 8)] (n, 3)] (* STB must be empty *)
         FiveStagePipelinePerformEdgeInterpretation;
     mkMicroopPath "CacheHitL2_pipe0"
         (StraightLine n [0; 1; 2; 3; 4])
         (FiveStagePipelineL1ComplPropagations_pipe0 n)
         [ReadsBetween AnyAccess (n, 8) (n, 3) (n, 9);
           FlushThread WritesOnly [(n, 6); (n, 8)] (n, 3)] (* STB must be empty *)
         FiveStagePipelinePerformEdgeInterpretation;
     mkMicroopPath "CacheMissReadL1_pipe0"
         (StraightLine n [0; 1; 2; 3; 4] ++ StraightLine n [6; 3; 7])
         (FiveStagePipelineL1ComplPropagations_pipe0 n)
         [FlushThread WritesOnly [(n, 6); (n, 8)] (n, 3)] (* STB must be empty *)
           FiveStagePipelinePerformEdgeInterpretation;
     mkMicroopPath "CacheMissReadL1L2_pipe0"
         (StraightLine n [0; 1; 2; 3; 4] ++ StraightLine n [8; 6; 3; 7] ++ StraightLine n [8; 9])
         (FiveStagePipelineL1ComplPropagations_pipe0 n)
         [FlushThread WritesOnly [(n, 6); (n, 8)] (n, 3)] (* STB must be empty *)
           FiveStagePipelinePerformEdgeInterpretation;
     mkMicroopPath "CacheMissReadL2_pipe0"
         (StraightLine n [0; 1; 2; 3; 4] ++ StraightLine n [8; 3; 9])
         (FiveStagePipelineL1ComplPropagations_pipe0 n)
         [FlushThread WritesOnly [(n, 6); (n, 8)] (n, 3)] (* STB must be empty *)
           FiveStagePipelinePerformEdgeInterpretation;
     mkMicroopPath "ReadFromStoreBuffer_pipe1"
         (StraightLine n [0; 1; 10; 11; 12])
         (FiveStagePipelineL1ComplPropagations_pipe1 n)
         [ReadsBetween WritesOnly (n, 11) (n, 11) (n, 6)]
           FiveStagePipelinePerformEdgeInterpretation;
     mkMicroopPath "CacheHitL1_pipe1"
         (StraightLine n [0; 1; 10; 11; 12])
         (FiveStagePipelineL1ComplPropagations_pipe1 n)
         [ReadsBetween AnyAccess (n, 6) (n, 11) (n, 7);
           FlushThread WritesOnly [(n, 6); (n, 8)] (n, 11)] (* STB must be empty *)
         FiveStagePipelinePerformEdgeInterpretation;
     mkMicroopPath "CacheHitL2_pipe1"
         (StraightLine n [0; 1; 10; 11; 12])
         (FiveStagePipelineL1ComplPropagations_pipe1 n)
         [ReadsBetween AnyAccess (n, 8) (n, 11) (n, 9);
           FlushThread WritesOnly [(n, 6); (n, 8)] (n, 11)] (* STB must be empty *)
         FiveStagePipelinePerformEdgeInterpretation;
     mkMicroopPath "CacheMissReadL1_pipe1"
         (StraightLine n [0; 1; 10; 11; 12] ++ StraightLine n [6; 11; 7])
         (FiveStagePipelineL1ComplPropagations_pipe1 n)
         [FlushThread WritesOnly [(n, 6); (n, 8)] (n, 11)] (* STB must be empty *)
           FiveStagePipelinePerformEdgeInterpretation;
     mkMicroopPath "CacheMissReadL1L2_pipe1"
         (StraightLine n [0; 1; 10; 11; 12] ++ StraightLine n [8; 6; 11; 7] ++ StraightLine n [8; 9])
         (FiveStagePipelineL1ComplPropagations_pipe1 n)
         [FlushThread WritesOnly [(n, 6); (n, 8)] (n, 11)] (* STB must be empty *)
           FiveStagePipelinePerformEdgeInterpretation;
     mkMicroopPath "CacheMissReadL2_pipe1"
         (StraightLine n [0; 1; 10; 11; 12] ++ StraightLine n [8; 11; 9])
         (FiveStagePipelineL1ComplPropagations_pipe1 n)
         [FlushThread WritesOnly [(n, 6); (n, 8)] (n, 11)] (* STB must be empty *)
           FiveStagePipelinePerformEdgeInterpretation
     ]
 | Write _ _ => [
     mkMicroopPath "WriteL1L2_pipe0"
       (StraightLine n [0; 1; 2; 3; 4; 5; 6; 7; 8; 9])
       (FiveStagePipelineL1ComplPropagations_pipe0 n)
       []
       FiveStagePipelinePerformEdgeInterpretation;
     mkMicroopPath "WriteL1_pipe0"
       (StraightLine n [0; 1; 2; 3; 4; 5; 6; 7])
       (FiveStagePipelineL1ComplPropagations_pipe0 n)
       []
       FiveStagePipelinePerformEdgeInterpretation;
     mkMicroopPath "WriteL2_pipe0"
       (StraightLine n [0; 1; 2; 3; 4; 5; 8; 9])
       (FiveStagePipelineL2ComplPropagations_pipe0 n)
       []
       FiveStagePipelinePerformEdgeInterpretation;
     mkMicroopPath "WriteL1L2_pipe1"
       (StraightLine n [0; 1; 10; 11; 12; 5; 6; 7; 8; 9])
       (FiveStagePipelineL1ComplPropagations_pipe1 n)
       []
       FiveStagePipelinePerformEdgeInterpretation;
     mkMicroopPath "WriteL1_pipe1"
       (StraightLine n [0; 1; 10; 11; 12; 5; 6; 7])
       (FiveStagePipelineL1ComplPropagations_pipe1 n)
       []
       FiveStagePipelinePerformEdgeInterpretation;
     mkMicroopPath "WriteL2_pipe1"
       (StraightLine n [0; 1; 10; 11; 12; 5; 8; 9])
       (FiveStagePipelineL2ComplPropagations_pipe1 n)
       []
       FiveStagePipelinePerformEdgeInterpretation
     ]
 | Fence _   => [
     mkMicroopPath "Fence_pipe0"
       (StraightLine n [0; 1; 2; 3; 4])
       (FiveStagePipelineL2ComplPropagations_pipe0 n)
       [FlushThread WritesOnly [(n, 6); (n, 8)] (n, 2)]
       FiveStagePipelinePerformEdgeInterpretation;
    mkMicroopPath "Fence_pipe1"
       (StraightLine n [0; 1; 10; 11; 12])
       (FiveStagePipelineL2ComplPropagations_pipe1 n)
       [FlushThread WritesOnly [(n, 6); (n, 8)] (n, 10)]
       FiveStagePipelinePerformEdgeInterpretation
     ]
 end.

Definition FiveStageSSProcessor
  (num_cores : nat)
  : Processor :=
  let p n := mkPipeline "FiveStagePipeline" n [6; 8]
    (FiveStagePipelineMicroopPaths n) FiveStagePipelineStages in
  mkProcessor "FiveStageSSProcessor" (fun _ => true) (map p (Range num_cores)).

