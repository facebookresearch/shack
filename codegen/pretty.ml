(*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 *)

open Ast

let fmt_kw ppf s = Format.fprintf ppf "%s" s
let fmt_str ppf s = Format.fprintf ppf "\"%s\"" s
let fmt_int ppf n = Format.fprintf ppf "%d" n
let fmt_bool ppf b = Format.fprintf ppf "%b" b

let fmt_list fa ppf xs =
  let semi ppf () = Format.fprintf ppf "@ ; " in
  Format.fprintf ppf "@[<v>[%a]@]" (Format.pp_print_list ~pp_sep:semi fa) xs

let rec fmt_ty ppf = function
  (* Keep this one in sync with the prelude *)
  | ArrayKey -> Format.fprintf ppf "%a" fmt_kw "arraykey"
  | IntT -> Format.fprintf ppf "%a" fmt_kw "IntT"
  | BoolT -> Format.fprintf ppf "%a" fmt_kw "BoolT"
  | NothingT -> Format.fprintf ppf "%a" fmt_kw "NothingT"
  | MixedT -> Format.fprintf ppf "%a" fmt_kw "MixedT"
  | ClassT { name; tyargs } ->
      Format.fprintf ppf "@[ClassT@ ";
      Format.fprintf ppf "true@ ";
      Format.fprintf ppf "%a@ " fmt_str name;
      Format.fprintf ppf "%a@]" (fmt_list fmt_ty) tyargs
  | NullT -> Format.fprintf ppf "%a" fmt_kw "NullT"
  | NonNullT -> Format.fprintf ppf "%a" fmt_kw "NonNullT"
  | UnionT (s, t) ->
      Format.fprintf ppf "@[UnionT@ (%a)@ (%a)@]" fmt_ty s fmt_ty t
  | InterT (s, t) ->
      Format.fprintf ppf "@[InterT@ (%a)@ (%a)@]" fmt_ty s fmt_ty t
  | GenT (n, _) -> Format.fprintf ppf "@[GenT@ %a@]" fmt_int n
  | DynamicT -> Format.fprintf ppf "%a" fmt_kw "DynamicT"
  | SupportDynT -> Format.fprintf ppf "%a" fmt_kw "SupportDynT"

let lang_ty_pretty ty = Format.asprintf "%a" fmt_ty ty
let fmt_binop ppf op = Format.fprintf ppf "%a" fmt_kw (show_binop op)
let fmt_uninop ppf op = Format.fprintf ppf "%a" fmt_kw (show_uniop op)

let rec fmt_expr ppf = function
  | IntE n -> Format.fprintf ppf "@[IntE@ %a@]" fmt_int n
  | BoolE b -> Format.fprintf ppf "@[BoolE@ %a@]" fmt_bool b
  | NullE -> Format.fprintf ppf "%a" fmt_kw "NullE"
  | BinOpE { op; lhs; rhs } ->
      Format.fprintf ppf "@[BinOpE@ %a@ (%a)@ (%a)@]" fmt_binop op fmt_expr lhs
        fmt_expr rhs
  | UniOpE { op; e } ->
      Format.fprintf ppf "@[UniOpE@ %a@ (%a)@]" fmt_uninop op fmt_expr e
  | VarE s -> Format.fprintf ppf "@[VarE %a@]" fmt_str s
  | ThisE -> Format.fprintf ppf "%a" fmt_kw "ThisE"
  | UpcastE { e; ty } ->
      Format.fprintf ppf "@[Upcast@ (%a)@ (%a)@]" fmt_expr e fmt_ty ty

let expr_pretty expr = Format.asprintf "%a" fmt_expr expr

let fmt_rtc ppf = function
  | RCTag s -> Format.fprintf ppf "@[RCTag@ %a@]" fmt_str s
  | RCInt -> Format.fprintf ppf "%a" fmt_kw "RCInt"
  | RCBool -> Format.fprintf ppf "%a" fmt_kw "RCBool"
  | RCNull -> Format.fprintf ppf "%a" fmt_kw "RCNull"
  | RCNonNull -> Format.fprintf ppf "%a" fmt_kw "RCNonNull"

let fmt_map fa ppf xs =
  let semi ppf () = Format.fprintf ppf "@ ; " in
  let fa ppf (k, v) = Format.fprintf ppf "@[%a@ :=@ %a@]" fmt_str k fa v in
  match xs with
  | [] -> Format.fprintf ppf "%a" fmt_kw "∅"
  | _ -> Format.fprintf ppf "@[<v>{[%a]}@]" (Format.pp_print_list ~pp_sep:semi fa) xs

let rec fmt_cmd ppf = function
  | SkipC -> Format.fprintf ppf "%a" fmt_kw "SkipC"
  | SeqC { fstc; sndc } ->
      Format.fprintf ppf "@[<v 2>SeqC@ (%a)@ (%a)@]" fmt_cmd fstc fmt_cmd sndc
  | LetC { lhs; e } ->
      Format.fprintf ppf "@[LetC@ %a@ (%a)@]" fmt_str lhs fmt_expr e
  | IfC { cond; thn; els } ->
      Format.fprintf ppf "@[IfC@ (%a)@ (%a)@ (%a)@]" fmt_expr cond fmt_cmd thn
        fmt_cmd els
  | GetC { lhs; recv; name } ->
      Format.fprintf ppf "@[GetC@ %a@ (%a)@ %a@]" fmt_str lhs fmt_expr recv
        fmt_str name
  | SetC { recv; name; rhs } ->
      Format.fprintf ppf "@[SetC@ (%a)@ %a@ (%a)@]" fmt_expr recv fmt_str name
        fmt_expr rhs
  | ErrorC -> Format.fprintf ppf "%a" fmt_kw "ErrorC"
  | CallC { lhs; recv; name; args } ->
      Format.fprintf ppf "@[CallC@ %a@ (%a)@ " fmt_str lhs fmt_expr recv;
      Format.fprintf ppf "%a@ " fmt_str name;
      Format.fprintf ppf "%a@]" (fmt_map fmt_expr) args
  | NewC { lhs; name; ty_args; args } ->
      Format.fprintf ppf "@[NewC@ %a@ %a@ " fmt_str lhs fmt_str name;
      (match ty_args with
      | [] -> Format.fprintf ppf "%a@ " fmt_kw "None"
      | _ -> Format.fprintf ppf "(@[Some@ %a@])@ " (fmt_list fmt_ty) ty_args);
      Format.fprintf ppf "%a@]" (fmt_map fmt_expr) args
  | RuntimeCheckC { v; rc; thn; els } ->
      ignore v;
      ignore rc;
      ignore thn;
      ignore els;
      failwith "RTC"

let cmd_pretty cmd = Format.asprintf "%a" fmt_cmd cmd
let mk_mdef_name cname name = Printf.sprintf "%s_%s" cname name

let fmt_mdef cname ppf { name; args; return_type; body; return } =
  Format.fprintf ppf "@[<v 2>%a %a := {|@," fmt_kw "Definition" fmt_kw
    (mk_mdef_name cname name);
  Format.fprintf ppf "@[%a := " fmt_kw "methodargs";
  Format.fprintf ppf "%a" (fmt_map fmt_ty) args;
  Format.fprintf ppf ";@]@,";
  Format.fprintf ppf "@[%a@ :=@ %a;@]@," fmt_kw "methodrettype" fmt_ty
    return_type;
  Format.fprintf ppf "@[%a@ :=@ %a;@]@," fmt_kw "methodbody" fmt_cmd body;
  Format.fprintf ppf "@[%a@ :=@ %a;@]@," fmt_kw "methodret" fmt_expr return;
  Format.fprintf ppf "@[%a@ :=@ %a;@]@." fmt_kw "methodvisibility" fmt_kw
    "Public" (*TODO*);
  Format.fprintf ppf "|}."

let mdef_pretty cname mdef = Format.asprintf "%a" (fmt_mdef cname) mdef

let fmt_field ppf (vis, ty) =
  Format.fprintf ppf "@[(%a, %a)@]" fmt_kw (show_visibility vis) fmt_ty ty

let fmt_variance ppf var = Format.fprintf ppf "%a" fmt_kw (show_variance var)

let fmt_constraints ppf (l, r) =
  Format.fprintf ppf "@[(%a,@ %a)@]" fmt_ty l fmt_ty r

let fmt_cdef ppf { name; generics; constraints; super; fields; methods } =
  let cs =
    List.flatten
    @@ List.map
         (fun (var, l, r) ->
           match var with
           | Eq -> [ (l, r); (r, l) ]
           | As -> [ (l, r) ]
           | Super -> [ (r, l) ])
         constraints
  in
  let generics = List.map fst generics in
  let mnames =
    List.map (fun (mname, _) -> (mname, mk_mdef_name name mname)) methods
  in
  Format.fprintf ppf "@[<v 2>%a %a := {|@," fmt_kw "Definition" fmt_kw name;
  Format.fprintf ppf "@[%a@ :=@ " fmt_kw "superclass";
  (match super with
  | None -> Format.fprintf ppf "%a" fmt_kw "None"
  | Some (t, targs) ->
      Format.fprintf ppf "Some(%a, " fmt_str t;
      Format.fprintf ppf "%a)" (fmt_list fmt_ty) targs);
  Format.fprintf ppf ";@]@,";
  Format.fprintf ppf "@[%a@ := %a;@]@," fmt_kw "generics"
    (fmt_list fmt_variance) generics;
  Format.fprintf ppf "@[%a@ := %a;@]@," fmt_kw "constraints"
    (fmt_list fmt_constraints) cs;
  Format.fprintf ppf "@[%a@ := " fmt_kw "classfields";
  Format.fprintf ppf "%a" (fmt_map fmt_field) fields;
  Format.fprintf ppf ";@]@,";
  Format.fprintf ppf "@[%a := " fmt_kw "classmethods";
  Format.fprintf ppf "%a" (fmt_map fmt_kw) mnames;
  Format.fprintf ppf ";@]@.";
  Format.fprintf ppf "|}."

let cdef_pretty cdef = Format.asprintf "%a" fmt_cdef cdef

let rec gather = function
  | [] -> []
  | cdef :: rest ->
      let mdefs =
        List.map (fun (_, mdef) -> mdef_pretty cdef.name mdef) cdef.methods
      in
      List.append mdefs (cdef_pretty cdef :: gather rest)

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
   (* Generated from test.lang *)\n\n\
   Definition arraykey := UnionT IntT BoolT."

let program_pretty prog =
  let l = prelude :: gather prog in
  String.concat "\n\n" l
