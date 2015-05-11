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
Require Import Util.
Require Import Instruction.
Require Import Graph.

Import ListNotations.

Definition beq_nat_pair
  (a b : nat * nat)
  : bool :=
  andb (beq_nat (fst a) (fst b)) (beq_nat (snd a) (snd b)).

Definition beq_nat_triple
  (a b : nat * (nat * nat))
  : bool :=
  andb (beq_nat (fst a) (fst b)) (andb (beq_nat (fst (snd a)) (fst (snd b))) (beq_nat (snd (snd a)) (snd (snd b)))).

Definition WritesList : Set := list ((nat * nat) * (list Microop)).
Definition ReadsList : Set := list ((nat * (nat * nat)) * (list Microop)).

Definition SortWritesHelper
  (l : WritesList)
  (u : Microop)
  : WritesList :=
  match u with
  | mkMicroop g t n (Write a d) =>
      AppendToMatch (beq_nat_pair (a, d)) l (a, d) u
  | _ => l
  end.

Fixpoint SortWrites
  (p : list Microop)
  : WritesList :=
  fold_left SortWritesHelper p [].

Fixpoint FindWrites
  (l : WritesList)
  (a d : nat)
  : list Microop :=
  match l with
  | ((h1, h2), ws)::t =>
      if beq_nat_pair (h1, h2) (a, d)
      then ws
      else FindWrites t a d
  | [] => []
  end.

Definition SortReadsHelper
  (l : ReadsList)
  (u : Microop)
  : ReadsList :=
  match u with
  | mkMicroop g t n (Read a d) =>
      AppendToMatch (beq_nat_triple (a, (d, t))) l (a, (d, t)) u
  | _ => l
  end.

Fixpoint SortReads
  (p : list Microop)
  : ReadsList :=
  fold_left SortReadsHelper p [].

Fixpoint FindReads
  (l : ReadsList)
  (a d i : nat)
  (u : Microop)
  : list Microop :=
  match l with
  | ((h1, (h2, h3)), ws)::t =>
      if (beq_nat_triple (h1, (h2, h3)) (a, (d, i)))
      then (removeb (beq_uop u) ws)
      else FindReads t a d i u
  | [] => []
  end.

Fixpoint FindSourcesForReads
  (l : list Microop)
  (w : WritesList)
  (r : ReadsList)
  : list (list (option Microop * Microop)) :=
  match l with
  | h::t => match h with
            | mkMicroop g i n (Read a d) =>
                let f x := (Some x, h) in
                let l' := map f ((FindWrites w a d) ++
                (FindReads r a d i h)) in
                let l'' :=
                  if beq_nat O d
                  then (None, h) :: l'
                  else l' in
                l'' :: FindSourcesForReads t w r
            | _ => FindSourcesForReads t w r
            end
  | [] => []
  end.

Fixpoint FilterInvalidHelper3
  (l1 : list (option Microop * Microop))
  (op : option Microop * Microop)
  (l2 : list Microop)
  (i : nat)
  : bool :=
  match i, op with
  | S i', (Some u1, u2) =>
      match (u1, u2) with
      | (mkMicroop _ _ _ (Read _ _), mkMicroop _ _ _ (Read _ _)) =>
          (* The source is a read sourced by a read. Is its source on the chain of sources
             that we are currently looking at? *)
          match find (beq_uop u1) l2 with
          (* There is a cycle of dependencies between loads alone, and thus this scenario is invalid. *)
          | Some _ => false
          (* No cycle yet, add the load to the chain and check its source. *)
          | None => let f x := match x with
                               | (Some _, u) => beq_uop u u1
                               | _ => false
                               end in
                    match (find f l1) with
                    | Some y => FilterInvalidHelper3 l1 y (u2::l2) i'
                    | None => (* Error *) true
                    end
          end
      | _ => true
      end
  | _, _ => true
  end.

Fixpoint FilterInvalidHelper2
  (l1 : list (option Microop * Microop))
  (l2 : list (option Microop * Microop))
  : list (option Microop * Microop) :=
  match l2 with
  | [] => []
  (* The longest chain possible should be the length of l1. *)
  | h::t => if (FilterInvalidHelper3 l1 h [] (length l1)) then h::(FilterInvalidHelper2 l1 t)
            else FilterInvalidHelper2 l1 t
  end.

Definition FilterInvalidHelper1
  (l : list (option Microop * Microop))
  : list (option Microop * Microop) :=
  FilterInvalidHelper2 l l.

Definition FilterInvalidRFScenarios
  (l : list (list (option Microop * Microop)))
  : list (list (option Microop * Microop)) :=
  let f x := match x with
               | [] => true
               | _ => false
               end in
  removeb f (Map FilterInvalidHelper1 l).

Definition RFScenarios
  (l : list Microop)
  : list (list (option Microop * Microop)) :=
  FilterInvalidRFScenarios (CrossProduct (FindSourcesForReads l (SortWrites l) (SortReads l))).

Definition RFScenariosWithWrites
  (l : list Microop)
  (w : WritesList)
  (r : ReadsList)
  : list (list (option Microop * Microop)) :=
  FilterInvalidRFScenarios (CrossProduct (FindSourcesForReads l w r)).

(** **** [AllPermutationsHelper3] *)
(** Prepend [h] to each of the list in [ts].  If [ts] is empty, create a new
list with only [h]. *)
Definition AllPermutationsHelper3
  {A : Type}
  (h : A)
  (ts : list (list A))
  : list (list A) :=
  match ts with
  | [] => []
  | _ => map (cons h) ts
  end.

Module AllPermutationsHelper3Example.

Example e1: AllPermutationsHelper3 0 [[1; 2]; [3; 4]] =
  [[0; 1; 2]; [0; 3; 4]].
Proof.
  auto.
Qed.

Example e2: AllPermutationsHelper3 0 [] = [].
Proof.
  auto.
Qed.

End AllPermutationsHelper3Example.

Fixpoint AllPermutationsHelper2
  {A : Type}
  (a b : list A)
  : list (A * list A) :=
  match b with
  | h::t =>
      (** Ultimately: prepend [h] to each permutation of [a ++ t].
      This function returns the set of all [(h, a++t)] pairs *)
      (h, a ++ t) :: AllPermutationsHelper2 (a ++ [h]) t
  | [] => []
  end.

Module AllPermutationsHelper2Example.

Example e1: AllPermutationsHelper2 [0; 1; 2] [3; 4; 5] =
  [(3, [0; 1; 2; 4; 5]); (4, [0; 1; 2; 3; 5]); (5, [0; 1; 2; 3; 4])].
Proof.
  auto.
Qed.

Example e2: AllPermutationsHelper2 [] [0; 1] = [(0, [1]); (1, [0])].
Proof.
  auto.
Qed.

Example e3: AllPermutationsHelper2 [0; 1] [] = [].
Proof.
  auto.
Qed.

End AllPermutationsHelper2Example.

Fixpoint AllPermutationsHelper
  {A : Type}
  (i : nat)
  (l : list A)
  (valid_last_element : A -> bool)
  : list (list A) :=
  match (i, l) with
  | (S i', []) => []
  | (S i', [h]) =>
      if valid_last_element h
      then [[h]]
      else []
  | (S i', _) =>
      let p := AllPermutationsHelper2 [] l in
      let p' :=
        (** For each pairing of (h, others) returned by
        [AllPermutationsHelper2], recursively calculate the set of all
        permutations of "others", and then prepend [h] to each. *)
        map (fun x => AllPermutationsHelper3 (fst x)
          (AllPermutationsHelper i' (snd x) valid_last_element)) p in
      (** Flatten the list of all permutations *)
      fold_left (app_tail (A:=_)) p' []
  | (O, _) => []
  end.

Definition AllPermutations
  {A : Type}
  (valid_last_element : A -> bool)
  (l : list A)
  : list (list A) :=
  AllPermutationsHelper (length l) l valid_last_element.

Module AllPermutationsExample.

Example e1 : AllPermutations (fun _ => true) [0; 1; 2] =
  [[0; 1; 2]; [0; 2; 1]; [1; 0; 2]; [1; 2; 0]; [2; 0; 1]; [2; 1; 0]].
Proof.
  auto.
Qed.

Example e2 : AllPermutations (beq_nat 2) [0; 1; 2] =
  [[0; 1; 2]; [1; 0; 2]].
Proof.
  auto.
Qed.

End AllPermutationsExample.

Fixpoint WritesByAddressHelper
  (l : list (nat * list (list Microop)))
  (w : WritesList)
  : list (nat * list (list Microop)) :=
  match w with
  | ((a, d), i) :: t =>
      WritesByAddressHelper (AppendToMatch (beq_nat a) l a i) t
  | [] => l
  end.

Definition WritesByAddress
  (w : WritesList)
  : list (list Microop) :=
  let f x := fold_left (app_tail (A:=_)) (snd x) [] in
  map f (WritesByAddressHelper [] w).

Fixpoint ValidWSScenario
  (last_values : list (Address * Data))
  (uop : Microop)
  : bool :=
  match uop with
  | mkMicroop _ _ _ (Write a d) =>
      match find (fun x => beq_nat a (fst x)) last_values with
      | Some (_, d') => beq_nat d d'
      | None => true (* If no last value was specified, anything is OK *)
      end
  | _ => false
  end.

Definition WSScenarios
  (w : WritesList)
  (last_values : list (Address * Data))
  : list (list (list Microop)) :=
  CrossProduct (map (AllPermutations (ValidWSScenario last_values)) (WritesByAddress w)).

Fixpoint FRScenarioHelper2
  (rf_w : Microop)
  (ws : list Microop)
  : option Microop :=
  let f x := match x with
  | Some y => Some y
  | None => None
  end in
  match ws with
  | h::t =>
      if beq_uop rf_w h
      then f (hd_error t)
      else FRScenarioHelper2 rf_w t
  | [] => None
  end.

Fixpoint FRScenarioHelper
  (rf_w : Microop)
  (wss : list (list Microop))
  : option Microop :=
  match (rf_w, wss) with
  | (mkMicroop _ _ _ (Write a1 _), h::t) =>
      match hd_error h with
      | Some (mkMicroop _ _ _ (Write a2 _)) =>
          if beq_nat a1 a2
          then FRScenarioHelper2 rf_w h
          else FRScenarioHelper rf_w t
      | _ => FRScenarioHelper rf_w t
      end
  | _ => None
  end. 

Fixpoint FRScenarioHelperInitial
  (rf_r : Microop)
  (wss : list (list Microop))
  : option Microop :=
  match (rf_r, wss) with
  | (mkMicroop _ _ _ (Read a1 _), h::t) =>
      match hd_error h with
      | Some (mkMicroop g i n (Write a2 d)) =>
          if beq_nat a1 a2
          then Some (mkMicroop g i n (Write a2 d))
          else FRScenarioHelperInitial rf_r t
      | _ => FRScenarioHelperInitial rf_r t
      end
  | _ => None
  end. 

Fixpoint FRScenario
  (rfs : list (option Microop * Microop))
  (wss : list (list Microop))
  : list (Microop * Microop) :=
  match rfs with
  | (Some w, r)::t =>
      match FRScenarioHelper w wss with
      | Some w' => (r, w') :: FRScenario t wss
      | None    =>            FRScenario t wss
      end
  | (None, r)::t =>
      match FRScenarioHelperInitial r wss with
      | Some w' => (r, w') :: FRScenario t wss
      | None    =>            FRScenario t wss
      end
  | [] => []
  end.

Fixpoint RFWSFRScenariosHelper2
  (rfs : list (option Microop * Microop))
  (wss : list (list (list Microop)))
  : list (
      list (option Microop * Microop) *
      list (list Microop) *
      list (Microop * Microop)) :=
  match wss with
  | h::t =>
      let fr := FRScenario rfs h in
      (rfs, h, fr) :: RFWSFRScenariosHelper2 rfs t
  | [] => []
  end.

Fixpoint RFWSFRScenariosHelper
  (rfs : list (list (option Microop * Microop)))
  (wss : list (list (list Microop)))
  : list (
      list (option Microop * Microop) *
      list (list Microop) *
      list (Microop * Microop)) :=
  match rfs with
  | h::t =>
      RFWSFRScenariosHelper2 h wss ++ RFWSFRScenariosHelper t wss
  | [] => []
  end.

Definition RFWSFRScenarios
  (last_values : list (Address * Data))
  (p : list Microop)
  : list (
      list (option Microop * Microop) *
      list (list Microop) *
      list (Microop * Microop)) :=
  let w := SortWrites p in
  let r := SortReads p in
  RFWSFRScenariosHelper (RFScenariosWithWrites p w r) (WSScenarios w last_values).

Module ExecutionExamples.

Definition e2Microops := [
    mkMicroop 0 0 0 (Write 0 0);
    mkMicroop 1 0 0 (Write 1 1);
    mkMicroop 2 1 0 (Read  0 0)].

Example e2a :
  FindSourcesForReads e2Microops (SortWrites e2Microops) (SortReads e2Microops)
  = [[(None, mkMicroop 2 1 0 (Read 0 0));
     (Some (mkMicroop 0 0 0 (Write 0 0)), mkMicroop 2 1 0 (Read 0 0))]
    ].
Proof.
auto.
Qed.

Example e2b :
  RFScenarios e2Microops
  = [
      [(None, mkMicroop 2 1 0 (Read 0 0))];
      [(Some (mkMicroop 0 0 0 (Write 0 0)), mkMicroop 2 1 0 (Read 0 0))]
    ].
Proof.
auto.
Qed.

Example e2c :
  WSScenarios (SortWrites e2Microops) []
  = [
      [[mkMicroop 0 0 0 (Write 0 0)];
       [mkMicroop 1 0 0 (Write 1 1)]]
    ].
Proof.
auto.
Qed.

Example e2d :
  WSScenarios (SortWrites e2Microops) [(1, 2)]
  = [].
Proof.
auto.
Qed.

Example e2e :
  RFWSFRScenarios [] e2Microops
  = [
  ([(None, mkMicroop 2 1 0 (Read 0 0))],
   [[mkMicroop 0 0 0 (Write 0 0)]; [mkMicroop 1 0 0 (Write 1 1)]],
   [(mkMicroop 2 1 0 (Read 0 0), mkMicroop 0 0 0 (Write 0 0))]);
  ([(Some (mkMicroop 0 0 0 (Write 0 0)), mkMicroop 2 1 0 (Read 0 0))],
   [[mkMicroop 0 0 0 (Write 0 0)]; [mkMicroop 1 0 0 (Write 1 1)]],
   [])
   ].
Proof.
auto.
Qed.

Example e3 :
  WSScenarios (SortWrites [
    mkMicroop 0 0 0 (Write 0 1);
    mkMicroop 1 0 0 (Write 1 1);
    mkMicroop 2 1 0 (Write 0 2)]) []
  = [
  [[mkMicroop 2 1 0 (Write 0 2);
    mkMicroop 0 0 0 (Write 0 1)];
   [mkMicroop 1 0 0 (Write 1 1)]];
  [[mkMicroop 0 0 0 (Write 0 1);
    mkMicroop 2 1 0 (Write 0 2)];
   [mkMicroop 1 0 0 (Write 1 1)]]
  ].
Proof.
auto.
Qed.

End ExecutionExamples.
