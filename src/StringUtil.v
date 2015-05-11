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

Import ListNotations.
Open Scope string_scope.

Definition tab := String (ascii_of_nat 9) "".
Definition newline := String (ascii_of_nat 10) "".
Definition quote := String (ascii_of_nat 34) "".

Definition stringOfNat'' (n : nat) : string :=
  String (ascii_of_nat (nat_of_ascii "0" + n)) "".

Fixpoint stringOfNat' (n tens ones : nat) : string :=
  match (n, tens, ones) with
  | (S n', _, S (S (S (S (S (S (S (S (S (S ones')))))))))) =>
    stringOfNat' n' (S tens) ones'
  | (S n', S t', _) => stringOfNat' n' 0 tens ++ stringOfNat'' ones
  | (S n', 0, _) => stringOfNat'' ones
  | _ => "(overflow)"
  end.

Definition stringOfNat (n : nat) : string :=
  stringOfNat' (S n) 0 n.

Definition StringOf
  (l : list string)
  : string :=
  fold_left append l "".

Fixpoint beq_string
  (s1 s2 : string)
  : bool :=
  match (s1, s2) with
  | (String h1 t1, String h2 t2) =>
      if beq_nat (nat_of_ascii h1) (nat_of_ascii h2)
      then beq_string t1 t2
      else false
  | (EmptyString, EmptyString) => true
  | _ => false
  end.

