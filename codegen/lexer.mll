 {
  open Core
  open Lexing
  open Parser
}

let digits = ['0' - '9']
let alpha = ['a' - 'z' 'A' - 'Z']
let white = ['\t' ' ']
let newline = '\r' | '\n' | "\r\n"

rule lexer = parse
  | "//"  [^ '\r' '\n']* newline+ { new_line lexbuf; lexer lexbuf }
  | eof { Eof }
  | newline { new_line lexbuf; lexer lexbuf }
  | white+ { lexer lexbuf }
  | "$" { Dollar }
  | "@" { Exact }
  | "arraykey" { ArrayKey }
  | "error" { ErrorCmd }
  | "new" { New }
  | "is" { Is }
  | "let" { Let }
  | "function" { Function }
  | "return" { Return }
  | "class" { Class }
  | "extends" { Extends }
  | "where" { Where }
  | "as" { As }
  | "super" { Super }
  | "public" { Public }
  | "private" { Private }
  | "if" { If }
  | "then" { Then }
  | "else" { Else }
  | "upcast" { Upcast }
  | "," { Comma }
  | ":" { Colon}
  | ";" { Semi }
  | "(" { LPar }
  | ")" { RPar }
  | "{" { LBrace }
  | "}" { RBrace }
  | "+" { Plus }
  | "-" { Minus }
  | "*" { Times }
  | "/" { Div }
  | "=" { Eq }
  | "!" { Not }
  | "<" { Lt }
  | ">" { Gt }
  | "&" { Ampersand }
  | "|" { Pipe }
  | "#" { Hash }
  | "->" { Arrow }
  | "true" { True }
  | "false" { False }
  | "int" { IntT }
  | "bool" { Bool }
  | "null" { Null }
  | "nonnull" { Nonnull }
  | "mixed" { Mixed }
  | "nothing" { Nothing }
  | "dynamic" { Dynamic }
  | digits (digits | '_')* as n { Int (int_of_string n) }
  | alpha (alpha | digits | '_')* as v { Id v }
