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
Require Import StringUtil.
Require Import Ascii.

Import ListNotations.
Open Scope string_scope.

(** * Debugging functions *)

(** ** [Printf] *)
(** The semantics of [Printf] are a little weird due to the Coq to OCaml
extraction process.  The semantics are as follows: if the environment variable
<<PIPEGRAPH_DEBUG>> is set, then the string [s] will be printed to stdout.  The
argument [a] is returned either way, and the returned value must be used by
some later function to ensure that the [Printf] doesn't get optimized away
during extraction. *)
Definition Printf
  {A : Type}
  (x : A)
  (s : string)
  : A :=
  x.

Definition Println
  {A : Type}
  (x : A)
  (l : list string)
  : A :=
  Printf x (StringOf (l ++ [newline])).

(** ** [Warning] *)
(** The semantics of [Warning] are a little weird due to the Coq to OCaml
extraction process.  Print [s] to stdout (regardless of the environment
variable <<PIPEGRAPH_DEBUG>>.  The argument [a] is returned, and the returned
value must be used by some later function to ensure that the [Warning] doesn't
get optimized away during extraction. *)
Definition WarningHelper
  {A : Type}
  (x : A)
  (s : string)
  : A :=
  x.

Definition Warning
  {A : Type}
  (x : A)
  (ss : list string)
  : A :=
  WarningHelper x (StringOf ((newline :: "WARNING: " :: ss) ++ [newline; newline])).

