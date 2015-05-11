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

Require Import String.
Require Import Arith.

(** ** Basic Type Definitions *)
Definition InstID := nat.
Definition ThreadID := nat.
Definition IntraInstructionID := nat.
Definition Address := nat.
Definition Data := nat.
Definition FenceType := string.

(** ** Instructions *)

(** *** [MemoryAccess] *)
(** A [MemoryAccess] is the part of the [Microop] data structure representing
interaction with the memory system. *)
Inductive MemoryAccess : Set :=
| Read  : Address -> Data -> MemoryAccess
| Write : Address -> Data -> MemoryAccess
| Fence : FenceType       -> MemoryAccess
(* LL/SC, etc. *).

(** *** [Microop] *)
(** A [Microop] is either an instruction or part of an instruction.  Each
[Microop] has a globally unique ID [globalID], a thread ID [threadID], an
intra-instruction ID [intraInstructionID] (for when a single macroinstruction
has multiple microops), and a [MemoryAccess] [access] describing the memory
semantics. *)
Record Microop : Set := mkMicroop {
  globalID : InstID;
  threadID : ThreadID;
  intraInstructionID : IntraInstructionID;
  access : MemoryAccess
}.

(** *** [MicroopsAccessSameAddress] *)
Definition MicroopsAccessSameAddress
  (x y : Microop)
  : bool :=
  let ax :=
    match x with
    | mkMicroop _ _ _ (Read  a _) => Some a
    | mkMicroop _ _ _ (Write a _) => Some a
    | _ => None
    end in
  let ay :=
    match y with
    | mkMicroop _ _ _ (Read  a _) => Some a
    | mkMicroop _ _ _ (Write a _) => Some a
    | _ => None
    end in
  match (ax, ay) with
  | (Some ax', Some ay') => beq_nat ax' ay'
  | _ => false
  end.

(** *** [beq_uop] *)
(** Boolean equality check for two [Microop]s. *)
Definition beq_uop
  (a b : Microop)
  : bool :=
  match (a, b) with
  | (mkMicroop ga ta ia _, mkMicroop gb tb ib _) =>
      andb (beq_nat ga gb) (andb (beq_nat ta tb) (beq_nat ia ib))
  end.

(** ** [Thread]s and [Program]s *)
(** A [Thread] is a list of [Microop]s.  A [Program] is a list of [Thread]s. *)
Definition Thread : Set := list Microop.

Definition Program : Set := list Thread.

