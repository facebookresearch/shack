(*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 *)

open Core
open Errors

let prelude =
  "(*\n\
  \ * Copyright (c) Meta Platforms, Inc. and affiliates.\n\
  \ *\n\
  \ * This source code is licensed under the MIT license found in the\n\
  \ * LICENSE file in the root directory of this source tree.\n\
  \ *)\n\
   From stdpp Require Import base strings gmap stringmap fin_maps.\n\n\
   From iris.proofmode Require Import tactics.\n\
   From iris.base_logic.lib Require Import iprop own wsat.\n\
   From iris.algebra.lib Require Import gmap_view.\n\n\
   From shack Require Import lang progdef subtype ok typing.\n\
   From shack Require Import eval heap modality interp soundness.\n\n\
   From shack.reflect Require Import progdef.\n\n\
   (* Generated from test.lang *)\n\n\
   Definition arraykey := UnionT IntT BoolT."

let mk_PDC prog =
  let names =
    List.map
      ~f:(fun cdef ->
        let name = cdef.Ast.name in
        Printf.sprintf "\"%s\" := %s" name name)
      prog
  in
  let s = String.concat ~sep:"; " names in
  [
    "Definition pdefs0 : stringmap classDef :=";
    Printf.sprintf "  {[ %s ]}." s;
    "Local Instance PDC : ProgDefContext := { pdefs := pdefs0 }.";
    "Lemma pacc_compute:\n\
    \  Forall\n\
    \  (uncurry (λ (c : tag) (_ : classDef), Acc (λ x y : tag, extends y x) c))\n\
    \  (map_to_list pdefs).\n\
     Proof.\n\
    \  rewrite /pdefs /= /pdefs0.\n\
    \  apply pacc_helper.\n\
    \  vm_compute map_to_list.\n\
    \  simpl.\n\
    \  rewrite Forall_lookup => k c /=.\n\
    \  by repeat (rewrite /lookup /=; step_pacc).\n\
     Qed.";
    "Local Instance PDA : ProgDefAcc  := { pacc := pacc pacc_compute }.";
  ]

let process prog =
  let l = [ prelude; Pretty.program_pretty prog ] in
  let l = l @ mk_PDC prog in
  String.concat ~sep:"\n\n" l

let process_cmd input_file output_file =
  try
    let inx = In_channel.create input_file in
    let lexbuf = Lexing.from_channel inx in
    let raw_term = Parser.prog Lexer.lexer lexbuf in
    let () = In_channel.close inx in
    let s = process raw_term in
    let () =
      match output_file with
      | None -> Printf.printf "%s\n" s
      | Some output_file ->
          let outx = Out_channel.create output_file in
          let () = Printf.fprintf outx "%s\n" s in
          let () = Out_channel.close outx in
          ()
    in
    ()
  with
  | TError (e, l, m) -> printf "Error: %s\n" (msg_of_error e l m)
  | Sys_error s -> printf "System Error: %s\n" s

let env =
  let open Cmdliner in
  let input_file =
    let doc = "path to an input file." in
    Arg.(
      required & opt (some string) None & info [ "f"; "file" ] ~doc ~docv:"FILE")
  in
  let output_file =
    let doc = "path to an output file. Will print on stdout if not provided." in
    Arg.(
      value
      & opt (some string) None
      & info [ "o"; "output" ] ~doc ~docv:"OUTPUT")
  in
  Term.(const process_cmd $ input_file $ output_file)

let main () =
  let open Cmdliner in
  let cmd =
    let doc = "parse Hack-like files and output Coq content for Shack." in
    let man =
      [
        `S Manpage.s_description;
        `P (String.strip {| Process Hack-like files for Shack." |});
      ]
    in
    let info = Cmd.info "codegen" ~version:"%%VERSION%%" ~doc ~man in
    Cmd.v info env
  in
  exit (Cmd.eval cmd)

let () = main ()
