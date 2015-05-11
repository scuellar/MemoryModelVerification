(******************************************************************************)
(* PipeCheck: Specifying and Verifying Microarchitectural                     *)
(* Enforcement of Memory Consistency Models                                   *)
(*                                                                            *)
(* Copyright (c) 2015 Daniel Lustig, Princeton University                     *)
(* All rights reserved.                                                       *)
(*                                                                            *)
(* This library is free software; you can redistribute it and/or              *)
(* modify it under the terms of the GNU Lesser General Public                 *)
(* License as published by the Free Software Foundation; either               *)
(* version 2.1 of the License, or (at your option) any later version.         *)
(*                                                                            *)
(* This library is distributed in the hope that it will be useful,            *)
(* but WITHOUT ANY WARRANTY; without even the implied warranty of             *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU          *)
(* Lesser General Public License for more details.                            *)
(*                                                                            *)
(* You should have received a copy of the GNU Lesser General Public           *)
(* License along with this library; if not, write to the Free Software        *)
(* Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA  02110-1301  *)
(* USA                                                                        *)
(******************************************************************************)

open Str
open Map
open PipeGraph

let rec pipegraphStringHelper s n l =
  try
    pipegraphStringHelper s (n+1) (String.get s n :: l)
  with Invalid_argument _ ->
    List.rev_append l []

let pipegraphString s = pipegraphStringHelper s 0 []

module AddressMap = Map.Make(String)

let addressMap = AddressMap.empty
let addressMap = AddressMap.add "x" 0 addressMap
let addressMap = AddressMap.add "y" 1 addressMap
let addressMap = AddressMap.add "z" 2 addressMap
let addressMap = AddressMap.add "w" 3 addressMap

let rec appendToNth l n a =
  match (l, n) with
  | (h::t, 0) -> (h @ [a])::t
  | (h::t, _) -> h :: appendToNth t (n-1) a
  | ([], 0) -> [[a]]
  | ([], _) -> [] :: appendToNth [] (n-1) a

let rec renumber_accesses_helper outer_left inner_left right new_eiid =
  flush stdout;
  match right with
  | h::t -> (
      match h with
      | hh::ht ->
          let hh' = {hh with globalID = new_eiid} in
          renumber_accesses_helper
            outer_left (inner_left @ [hh']) (ht::t) (new_eiid + 1)
      | [] ->
          renumber_accesses_helper
            (outer_left @ [inner_left]) [] t new_eiid)
  | [] -> outer_left

let renumber_accesses ops = renumber_accesses_helper [] [] ops 0

let access_of_line line old_uops =
  let d = Str.regexp "digraph" in
  try
    let _ = Str.search_forward d line 0 in
    true, []
  with
  Not_found -> ();
  let r = Str.regexp "eiid\\([0-9]+\\).*: \\(.*\\)..proc:\\([0-9]+\\)" in
  let rw_r          = Str.regexp "R\\([^*]\\)\\*?=\\(.\\)" in
  let rw_w_unlocked = Str.regexp "W\\([^*]\\)=\\(.\\)" in
  let rw_w_locked   = Str.regexp "W\\([^*]\\)\\*=\\(.\\)" in
  try
    let _ = Str.search_forward r line 0 in
    let eiid = int_of_string    (Str.matched_group 1 line)            in
    let rw   =                   Str.matched_group 2 line             in
    let proc = int_of_string    (Str.matched_group 3 line)            in
    let accesses =
      try
          let _ = Str.search_forward rw_r rw 0 in
          let addr = AddressMap.find  (Str.matched_group 1 rw) addressMap in
          let data = int_of_string    (Str.matched_group 2 rw)            in
          [Read (addr, data)]
      with Not_found ->
        try
          let _ = Str.search_forward rw_w_unlocked rw 0 in
          let addr = AddressMap.find  (Str.matched_group 1 rw) addressMap in
          let data = int_of_string    (Str.matched_group 2 rw)            in
          [Write (addr, data)]
        with Not_found ->
          try
            let _ = Str.search_forward rw_w_locked rw 0 in
            let addr = AddressMap.find  (Str.matched_group 1 rw) addressMap in
            let data = int_of_string    (Str.matched_group 2 rw)            in
            [Write (addr, data); Fence (pipegraphString "LOCK")]
          with Not_found ->
            [Fence (pipegraphString rw)]
      in
    let uop a = {globalID=eiid; threadID0=proc; intraInstructionID0=0; access=a} in
    let new_uops = map uop accesses in
    false, fold_left (fun l u -> appendToNth l (threadID0 u) u) new_uops old_uops
  with Not_found -> false, old_uops

let rec parse_herd_graph channel executions ops =
  try
    let line = input_line channel in
    let new_exec, ops' = access_of_line line ops in
    match new_exec with
    | false -> parse_herd_graph channel executions ops'
    | true  -> parse_herd_graph channel (executions @ [ops]) ops'
  with
    End_of_file ->
      Printf.printf "Test has %d instructions\n"
        (length (fold_left List.append ops []));
      map renumber_accesses (List.tl executions @ [ops])

let rec check_if_allowed channel =
  try
    let line = input_line channel in
    try
      let _ = Str.search_forward (regexp "Never") line 0 in
      (false, line)
    with Not_found ->
    try
      let _ = Str.search_forward (regexp "Sometimes") line 0 in
      (true, line)
    with Not_found ->
    try
      let _ = Str.search_forward (regexp "Always") line 0 in
      (true, line)
    with Not_found -> check_if_allowed channel
  with
    End_of_file ->
      raise (Failure "Could not parse herd output")

let rec get_line_final_memory_values l n r =
  try
    let last = Str.search_forward (regexp "\\(\\[[w-z]\\]\\)=\\([0-9]\\)") l n in
    let addr = AddressMap.find  (Str.matched_group 1 l) addressMap in
    let data = int_of_string    (Str.matched_group 2 l)            in
    get_line_final_memory_values l (last + 1) (PipeGraph.Pair (addr, data) :: r)
  with Not_found ->
    try
      let last = Str.search_forward (regexp "\\([w-z]\\)=\\([0-9]\\)") l n in
      let addr = AddressMap.find  (Str.matched_group 1 l) addressMap in
      let data = int_of_string    (Str.matched_group 2 l)            in
      get_line_final_memory_values l (last + 1) (PipeGraph.Pair (addr, data) :: r)
    with Not_found ->
      r

let rec get_final_memory_values channel r =
  try
    let line = input_line channel in
    get_final_memory_values channel (get_line_final_memory_values line 0 r)
  with End_of_file ->
    r

let execute_herd herd_path litmus_test_path model =
  let testfile = Unix.openfile litmus_test_path [Unix.O_RDONLY] 0 in
  let testchannel = Unix.in_channel_of_descr testfile in
  let final_memory_values = get_final_memory_values testchannel [] in

  (* Create a pipe for herd to feed its output into *)
  let (pipe_read_end, pipe_write_end) = Unix.pipe() in

  (* Run herd once with "-show prop" to check whether it considers the
     proposed output to be legal or not *)
  let args = Array.of_list ["herd"; "-show"; "prop"; litmus_test_path] in
  let pid = Unix.create_process herd_path args
    Unix.stdin pipe_write_end Unix.stderr in
  Unix.close pipe_write_end;
  let _ =
    (match Unix.waitpid [] pid with
    | (_, Unix.WEXITED 0) -> true
    | (_, Unix.WEXITED 127) ->
        raise (Failure "herd: command not found.  Did you add it to your path?")
    | _ -> raise (Failure "herd 1")) in
  let channel = Unix.in_channel_of_descr pipe_read_end in
  let (allowed, line) = check_if_allowed channel in
  Printf.printf "herd: allowed=%B: %s\n" allowed line;

  (* Make a temporary directory to hold the generated graphs *)
  let pipegraph_path = Filename.get_temp_dir_name() ^ "/pipegraph" in
  (try
     Unix.mkdir pipegraph_path 0o700
   with Unix.Unix_error (Unix.EEXIST, _, _) -> ());

  (* Run herd a second time with "-through all" to generate the graph(s) for
   the litmus test, whether they are permitted or not (PipeGraph will
   recheck). *)
  let (pipe2_read_end, pipe2_write_end) = Unix.pipe() in
  let args2 = Array.of_list
    ["herd"; "-show"; "prop"; "-through"; "all"; "-o"; pipegraph_path;
       "-model"; model; litmus_test_path] in
  let pid2 = Unix.create_process herd_path args2
    (Unix.descr_of_in_channel stdin)
    pipe2_write_end
    (Unix.descr_of_out_channel stderr) in
  Unix.close pipe2_write_end;
  let _ =
    (match Unix.waitpid [] pid2 with
    | (_, Unix.WEXITED 0) -> true
    | _ -> raise (Failure "herd 2")) in

  (* Read in the graph(s) produced by the second run of herd *)
  let herd_graph_filename = pipegraph_path ^ "/" ^
    (Filename.chop_extension (Filename.basename litmus_test_path)) ^ ".dot" in
  let herd_graph_descr = Unix.openfile herd_graph_filename [Unix.O_RDONLY] 0 in
  (allowed, final_memory_values,
    parse_herd_graph (Unix.in_channel_of_descr herd_graph_descr) [] []);;

