(*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 *)

open Core
open Errors

let process filename =
  try
    let inx = In_channel.create filename in
    let lexbuf = Lexing.from_channel inx in
    let () = Printf.printf "Parsing: %s\n" filename in
    let raw_term = Parser.prog Lexer.lexer lexbuf in
    let () = In_channel.close inx in
    let () = List.iter
        ~f:(fun d -> Printf.printf "%s\n" (Ast.show_classDef d))
        raw_term in
    ()
  with
  | TError (e, l, m) -> printf "Error: %s\n" (msg_of_error e l m)
  | Sys_error s -> printf "System Error: %s\n" s

let () =
  process "./test.lang"
