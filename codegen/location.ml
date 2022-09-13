type t = {startpos: Lexing.position; endpos: Lexing.position}

let dummy = {startpos= Lexing.dummy_pos; endpos= Lexing.dummy_pos}

type 'a loc = {item: 'a; loc: t}

(* (Format.formatter -> 'a -> unit) -> Format.formatter -> 'a loc -> unit *)
let pp_loc fmt ppf loc = fmt ppf loc.item

(* (Format.formatter -> 'a -> unit) -> 'a loc -> string *)
let show_loc fmt loc = Format.asprintf "%a" fmt loc.item

let mk startpos endpos = {startpos; endpos}

let mkloc item loc = {item; loc}

let dummy_loc = {startpos= Lexing.dummy_pos; endpos= Lexing.dummy_pos}

let mkdummy item = {item; loc= dummy_loc}
