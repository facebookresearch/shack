(*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 *)

open Core
open Errors

let process_cmd input_file output_file =
  try
    let inx = In_channel.create input_file in
    let lexbuf = Lexing.from_channel inx in
    let raw_term = Parser.prog Lexer.lexer lexbuf in
    let () = In_channel.close inx in
    let s = Pretty.program_pretty raw_term in
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
