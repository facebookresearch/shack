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
  | GenT of string
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
  fields : (visibility * lang_ty * string) list;
  methods : methodDef list;
}
[@@deriving show]

type program = classDef list [@@deriving show]
