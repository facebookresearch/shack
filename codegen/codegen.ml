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
    let raw_term = Parser.prog Lexer.lexer lexbuf in
    let () = In_channel.close inx in
    let () = Printf.printf "%s\n" @@ Pretty.program_pretty raw_term in
    (* let () = Printf.printf "%s\n" @@ Ast.show_program raw_term in *)
    ()
  with
  | TError (e, l, m) -> printf "Error: %s\n" (msg_of_error e l m)
  | Sys_error s -> printf "System Error: %s\n" s

let show_token token =
  let open Parser in
  match token with
  | Where -> "Where"
  | Upcast -> "Upcast"
  | True -> "True"
  | Times -> "Times"
  | Then -> "Then"
  | Super -> "Super"
  | Semi -> "Semi"
  | Return -> "Return"
  | RPar -> "RPar"
  | RBrace -> "RBrace"
  | Public -> "Public"
  | Private -> "Private"
  | Plus -> "Plus"
  | Pipe -> "Pipe"
  | Null -> "Null"
  | Nothing -> "Nothing"
  | Not -> "Not"
  | Nonnull -> "Nonnull"
  | New -> "New"
  | Mixed -> "Mixed"
  | Minus -> "Minus"
  | Lt -> "Lt"
  | Let -> "Let"
  | LPar -> "LPar"
  | LBrace -> "LBrace"
  | Is -> "Is"
  | IntT -> "IntT"
  | Int n -> sprintf "Int(%d)" n
  | If -> "If"
  | Id s -> sprintf "Id(%s)" s
  | Hash -> "Hash"
  | Gt -> "Gt"
  | Function -> "Function"
  | False -> "False"
  | Extends -> "Extends"
  | ErrorCmd -> "ErrorCmd"
  | Eq -> "Eq"
  | Eof -> "Eof"
  | Else -> "Else"
  | Dynamic -> "Dynamic"
  | Dollar -> "Dollar"
  | Div -> "Div"
  | Comma -> "Comma"
  | Colon -> "Colon"
  | Class -> "Class"
  | Bool -> "Bool"
  | As -> "As"
  | Arrow -> "Arrow"
  | Ampersand -> "Ampersand"

let is_eof = function
  | Some Parser.Eof -> true
  | _ -> false

let _process filename =
  try
    let inx = In_channel.create filename in
    let lexbuf = Lexing.from_channel inx in
    let token = ref None in
    while not (is_eof (!token)) do
      let tok = Lexer.lexer lexbuf in
      printf "%s\n" (show_token tok);
      token := Some tok;
    done;
    let () = In_channel.close inx in
    ()
  with
  | TError (e, l, m) -> printf "Error: %s\n" (msg_of_error e l m)
  | Sys_error s -> printf "System Error: %s\n" s
let () =
  process "./test.lang"
