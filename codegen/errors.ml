open Core

type t = LexingError | SyntaxError

exception TError of t * Location.t * string

let name_of_error = function
  | LexingError -> "Lexing error"
  | SyntaxError -> "Syntax error"

let raise_error err loc msg = raise @@ TError (err, loc, msg)
let lexing_error = raise_error LexingError
let syntax_error = raise_error SyntaxError

let msg_of_error e loc msg =
  let open Location in
  let open Lexing in
  let startpos, endpos = (loc.startpos, loc.endpos) in
  sprintf "%s:\n\tFrom line %d, column %d to line %d, column %d\n\t%s"
    (name_of_error e) startpos.pos_lnum
    (startpos.pos_cnum - startpos.pos_bol)
    endpos.pos_lnum
    (endpos.pos_cnum - endpos.pos_bol)
    msg
