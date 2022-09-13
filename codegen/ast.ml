(*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 *)

(* Important: keep in sync with the Coq files. This is not automated *)
type tag = string
[@@deriving eq, show]

type loc = int
[@@deriving eq, show]

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

type var = string
[@@deriving eq, show]

type binop =
  | PlusO | MinusO | TimesO | DivO | LtO | GtO | EqO
[@@deriving show]

type uniop = NotO
[@@deriving show]

type expr =
  | IntE of int
  | BoolE of bool
  | NullE
  | BinOpE of { op: binop; lhs: expr; rhs : expr }
  | UniOpE of { op: uniop; e: expr }
  | VarE of var
  | ThisE
  | UpcastE of { e: expr; ty :lang_ty }
[@@deriving show]

type runtime_check =
  | RCTag of tag
  | RCInt
  | RCBool
  | RCNull
  | RCNonNull
[@@deriving show]

(* TODO: module for show *)
module SMap = struct
  include Stdlib.Map.Make(String)
  let make_pp pp_key pp_data fmt x =
    Format.fprintf fmt "@[<hv 2>{";
    let bindings = bindings x in
    (match bindings with
    | [] -> ()
    | _ -> Format.fprintf fmt " ");
    ignore
      (List.fold_left
         (fun sep (key, data) ->
           if sep then Format.fprintf fmt ";@ ";
           Format.fprintf fmt "@[";
           pp_key fmt key;
           Format.fprintf fmt " ->@ ";
           pp_data fmt data;
           Format.fprintf fmt "@]";
           true)
         false
         bindings);
    (match bindings with
    | [] -> ()
    | _ -> Format.fprintf fmt " ");
    Format.fprintf fmt "}@]"

  let pp : (Format.formatter -> 'a -> unit) -> Format.formatter -> 'a t -> unit =
    (fun pp_data -> make_pp (fun fmt s -> Format.fprintf fmt "%S" s) pp_data)

  let show pp_data x = Format.asprintf "%a" (pp pp_data) x
end

type cmd =
  | SkipC
  | SeqC of { fstc: cmd; sndc : cmd }
  | LetC of { lhs: var; e : expr }
  | IfC of { cond : expr; thn: cmd; els: cmd }
  | CallC of {lhs: var; recv:expr; name:string; args: expr SMap.t }
  | NewC of { lhs:var; name: tag; ty_args : lang_ty list; args : expr SMap.t }
  | GetC of { lhs : var; recv: expr; name : string }
  | SetC of { recv: expr; name: string; rhs : expr }
  | RuntimeCheckC of {v: var; rc: runtime_check; thn : cmd; els: cmd }
  | ErrorC
[@@deriving show]

type methodDef = {
  name : string;
  args : lang_ty SMap.t;
  return_type : lang_ty;
  body : cmd;
  return : expr;
}
[@@deriving show]

type variance = Invariant | Covariant | Contravariant
[@@deriving show]

type visibility = Public | Private
[@@deriving show]

type constr = As | Super | Eq
[@@deriving show]

type ty_constraint = constr * lang_ty * lang_ty
[@@deriving show]

type classDef = {
  name : tag;
  (* variance of the generics *)
  generics: variance list;
  (* set of class level constraints *)
  constraints: ty_constraint list;
  super : (tag * lang_ty list) option;
  fields : (visibility * lang_ty) SMap.t;
  methods : methodDef SMap.t;
}
[@@deriving show]

type program = classDef list
[@@deriving show]
