(*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 *)

(* Important: keep in sync with the Coq files. This is not automated *)
type tag = string [@@deriving eq, show]
type loc = int [@@deriving eq, show]

(* TODO: exact types *)
type lang_ty =
  | IntT
  | BoolT
  | NothingT
  | MixedT
  | ClassT of { name : tag; tyargs : lang_ty list }
  | NullT
  | NonNullT
  | UnionT of lang_ty * lang_ty
  | InterT of lang_ty * lang_ty
  (* The parser sets 0's for any GenT. We'll replace them in a second phase *)
  | GenT of (int * string)
  | DynamicT
  | SupportDynT
[@@deriving show]

type var = string [@@deriving eq, show]

type binop = PlusO | MinusO | TimesO | DivO | LtO | GtO | EqO
[@@deriving show { with_path = false }]

type uniop = NotO [@@deriving show { with_path = false }]

type expr =
  | IntE of int
  | BoolE of bool
  | NullE
  | BinOpE of { op : binop; lhs : expr; rhs : expr }
  | UniOpE of { op : uniop; e : expr }
  | VarE of var
  | ThisE
  | UpcastE of { e : expr; ty : lang_ty }
[@@deriving show]

type runtime_check = RCTag of tag | RCInt | RCBool | RCNull | RCNonNull
[@@deriving show]

type cmd =
  | SkipC
  | SeqC of { fstc : cmd; sndc : cmd }
  | LetC of { lhs : var; e : expr }
  | IfC of { cond : expr; thn : cmd; els : cmd }
  | CallC of {
      lhs : var;
      recv : expr;
      name : string;
      args : (string * expr) list;
    }
  | NewC of {
      lhs : var;
      name : tag;
      ty_args : lang_ty list;
      args : (string * expr) list;
    }
  | GetC of { lhs : var; recv : expr; name : string }
  | SetC of { recv : expr; name : string; rhs : expr }
  | RuntimeCheckC of { v : var; rc : runtime_check; thn : cmd; els : cmd }
  | ErrorC
[@@deriving show]

(* TODO: visibility *)
type methodDef = {
  name : string;
  args : (string * lang_ty) list;
  return_type : lang_ty;
  body : cmd;
  return : expr;
}
[@@deriving show]

type variance = Invariant | Covariant | Contravariant
[@@deriving show { with_path = false }]

type visibility = Public | Private [@@deriving show { with_path = false }]
type constr = As | Super | Eq [@@deriving show]
type ty_constraint = constr * lang_ty * lang_ty [@@deriving show]

type classDef = {
  name : tag;
  (* variance of the generics *)
  generics : (variance * string) list;
  (* set of class level constraints *)
  constraints : ty_constraint list;
  super : (tag * lang_ty list) option;
  fields : (string * (visibility * lang_ty)) list;
  methods : (string * methodDef) list;
}
[@@deriving show]

type program = classDef list [@@deriving show]

exception UnknownGeneric of string

(* Take a source description and replaces all the type variable #T with
 * the right debruijn index. Make a few checks along the way.
 *)
let rec mk_dbruijn dbs = function
  | ClassT { name; tyargs } ->
      ClassT { name; tyargs = List.map (mk_dbruijn dbs) tyargs }
  | UnionT (s, t) -> UnionT (mk_dbruijn dbs s, mk_dbruijn dbs t)
  | InterT (s, t) -> InterT (mk_dbruijn dbs s, mk_dbruijn dbs t)
  | GenT (_, t) -> (
      match List.find_opt (fun (_, s) -> String.equal s t) dbs with
      | Some (n, _) -> GenT (n, t)
      | None -> raise (UnknownGeneric t))
  | ty -> ty

let rec mk_dbruijn_expr dbs = function
  | BinOpE { op; lhs; rhs } ->
      BinOpE
        { op; lhs = mk_dbruijn_expr dbs lhs; rhs = mk_dbruijn_expr dbs rhs }
  | UniOpE { op; e } -> UniOpE { op; e = mk_dbruijn_expr dbs e }
  | UpcastE { e; ty } ->
      UpcastE { e = mk_dbruijn_expr dbs e; ty = mk_dbruijn dbs ty }
  | e -> e

let rec mk_dbruijn_cmd dbs = function
  | SkipC -> SkipC
  | SeqC { fstc; sndc } ->
      SeqC { fstc = mk_dbruijn_cmd dbs fstc; sndc = mk_dbruijn_cmd dbs sndc }
  | LetC { lhs; e } -> LetC { lhs; e = mk_dbruijn_expr dbs e }
  | IfC { cond; thn; els } ->
      IfC
        {
          cond = mk_dbruijn_expr dbs cond;
          thn = mk_dbruijn_cmd dbs thn;
          els = mk_dbruijn_cmd dbs els;
        }
  | CallC { lhs; recv; name; args } ->
      CallC
        {
          lhs;
          recv = mk_dbruijn_expr dbs recv;
          name;
          args = List.map (fun (k, e) -> (k, mk_dbruijn_expr dbs e)) args;
        }
  | NewC { lhs; name; ty_args; args } ->
      NewC
        {
          lhs;
          name;
          ty_args = List.map (mk_dbruijn dbs) ty_args;
          args = List.map (fun (k, e) -> (k, mk_dbruijn_expr dbs e)) args;
        }
  | GetC { lhs; recv; name } ->
      GetC { lhs; recv = mk_dbruijn_expr dbs recv; name }
  | SetC { recv; name; rhs } ->
      SetC
        { recv = mk_dbruijn_expr dbs recv; name; rhs = mk_dbruijn_expr dbs rhs }
  | RuntimeCheckC { v; rc; thn; els } ->
      RuntimeCheckC
        { v; rc; thn = mk_dbruijn_cmd dbs thn; els = mk_dbruijn_cmd dbs els }
  | ErrorC -> ErrorC

(* (TODO) Update if we ever support method level generics *)
let mk_dbruijn_mdef dbs { name; args; return_type; body; return } =
  {
    name;
    args = List.map (fun (k, ty) -> (k, mk_dbruijn dbs ty)) args;
    return_type = mk_dbruijn dbs return_type;
    body = mk_dbruijn_cmd dbs body;
    return = mk_dbruijn_expr dbs return;
  }

exception DuplicatedGeneric of string

let rec mk_dbs n seen = function
  | [] -> []
  | (_, t) :: tl ->
      if List.exists (String.equal t) seen then raise (DuplicatedGeneric t)
      else (n, t) :: mk_dbs (n + 1) (t :: seen) tl

let mk_dbruijn_cdef { name; generics; constraints; super; fields; methods } =
  let dbs = mk_dbs 0 [] generics in
  (* (variance * var) list *)
  {
    name;
    generics;
    constraints =
      List.map
        (fun (c, l, r) -> (c, mk_dbruijn dbs l, mk_dbruijn dbs r))
        constraints;
    super =
      (match super with
      | None -> None
      | Some (t, targs) -> Some (t, List.map (mk_dbruijn dbs) targs));
    fields = List.map (fun (k, (v, ty)) -> (k, (v, mk_dbruijn dbs ty))) fields;
    methods = List.map (fun (k, mdef) -> (k, mk_dbruijn_mdef dbs mdef)) methods;
  }

let mk_dbruijn_program prog = List.map mk_dbruijn_cdef prog
