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
   From shack.reflect Require Import lang progdef subtype.\n\n\
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
    "Lemma pacc : ∀ c, Acc (λ x y, extends y x) c.\n\
     Proof.\n\
    \  apply check_acc_defs_correct with (n := 100).\n\
    \  by exact (I <: True).\n\
     Qed.";
    "Local Instance PDA : ProgDefAcc  := { pacc := pacc }.";
  ]

let mk_bounded () =
  let b0 =
    "Lemma wf_fields_bounded : map_Forall (λ _cname, wf_cdef_fields_bounded) \
     pdefs.\n\
     Proof.\n\
    \  apply wf_cdef_fields_bounded_context_correct.\n\
    \  by exact (I <: True).\n\
     Qed."
  in

  let b1 =
    "Lemma wf_methods_bounded : map_Forall (λ _cname, cdef_methods_bounded) \
     pdefs.\n\
     Proof.\n\
    \  apply cdef_methods_bounded_context_correct.\n\
    \  by exact (I <: True).\n\
     Qed."
  in

  let b2 =
    "Lemma wf_constraints_bounded : map_Forall (λ _cname, \
     wf_cdef_constraints_bounded) pdefs.\n\
     Proof.\n\
    \  apply wf_cdef_constraints_bounded_context_correct.\n\
    \  by exact (I <: True).\n\
     Qed."
  in
  [ b0; b1; b2 ]

let mk_wf () =
  let wf0 =
    "Lemma wf_fields_wf  : map_Forall (λ _cname, wf_cdef_fields_wf) pdefs.\n\
     Proof.\n\
    \  apply: wf_cdef_fields_wf_context_correct.\n\
    \  exact (I <: True).\n\
     Qed."
  in

  let wf1 =
    "Lemma wf_constraints_wf : map_Forall (λ _cname, wf_cdef_constraints_wf) \
     pdefs.\n\
     Proof.\n\
    \  apply: wf_cdef_constraints_wf_context_correct.\n\
    \  exact (I <: True).\n\
     Qed."
  in

  let wf2 =
    "Lemma wf_methods_wf : map_Forall (λ _cname, wf_cdef_methods_wf) pdefs.\n\
     Proof.\n\
    \  apply: wf_cdef_methods_wf_context_correct.\n\
    \  exact (I <: True).\n\
     Qed."
  in
  [ wf0; wf1; wf2 ]

let mk_mono () =
  let mono0 =
    "Lemma wf_fields_mono : map_Forall (λ _cname, wf_field_mono) pdefs.\n\
     Proof.\n\
    \  apply wf_fields_mono_correct.\n\
    \  exact (I <: True).\n\
     Qed."
  in

  let mono1 =
    "Lemma wf_methods_mono : map_Forall (λ _cname, wf_cdef_methods_mono) pdefs.\n\
     Proof.\n\
    \  apply wf_methods_mono_correct.\n\
    \  exact (I <: True).\n\
     Qed."
  in

  let mono2 =
    "Lemma wf_mono : map_Forall (λ _cname, wf_cdef_mono) pdefs.\n\
     Proof.\n\
    \  apply wf_mono_correct.\n\
    \  exact (I <: True).\n\
     Qed."
  in
  [ mono0; mono1; mono2 ]

let process prog =
  let l = [ prelude; Pretty.program_pretty prog ] in
  let l = l @ mk_PDC prog @ mk_bounded () @ mk_wf () @ mk_mono () in
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
