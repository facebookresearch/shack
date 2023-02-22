(*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 *)

open Ast

let fmt_kw ppf s = Format.fprintf ppf "%s" s
let fmt_str ppf s = Format.fprintf ppf "\"%s\"" s

let fmt_list fa ppf xs =
  let semi ppf () = Format.fprintf ppf "@ ; " in
  Format.fprintf ppf "@[<v>[%a]@]" (Format.pp_print_list ~pp_sep:semi fa) xs

let rec fmt_ty ppf = function
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
      Format.fprintf ppf "@[UnionT@ (@[%a@])@ (@[%a@])@]" fmt_ty s fmt_ty t
  | InterT (s, t) ->
      Format.fprintf ppf "@[InterT@ (@[%a@])@ (@[%a@])@]" fmt_ty s fmt_ty t
  | GenT s ->
      (* TODO deBruijn *)
      Format.fprintf ppf "@[GenT@ %a@]" fmt_str s
  | DynamicT -> Format.fprintf ppf "%a" fmt_kw "DynamicT"
  | SupportDynT -> Format.fprintf ppf "%a" fmt_kw "SupportDynT"

(* TODO remove *)
let lang_ty_pretty ty = Format.asprintf "%a" fmt_ty ty

let rec expr_pretty = function
  | IntE n -> Printf.sprintf "IntE %d" n
  | BoolE b -> Printf.sprintf "BoolE %b" b
  | NullE -> "NullE"
  | BinOpE { op; lhs; rhs } ->
      Printf.sprintf "BinOpE %s (%s) (%s)" (show_binop op) (expr_pretty lhs)
        (expr_pretty rhs)
  | UniOpE { op; e } ->
      Printf.sprintf "UniOpE %s (%s)" (show_uniop op) (expr_pretty e)
  | VarE s -> Printf.sprintf "VarE %s" s
  | ThisE -> "ThisE"
  | UpcastE { e; ty } ->
      Printf.sprintf "Upcast (%s) (%s)" (expr_pretty e) (lang_ty_pretty ty)

let runtime_check_pretty = function
  | RCTag s -> Printf.sprintf "RCTag \"%s\"" s
  | RCInt -> "RCInt"
  | RCBool -> "RCBool"
  | RCNull -> "RCNull"
  | RCNonNull -> "RCNonNull"

let pretty_map p xs =
  let xs =
    List.map (fun (key, v) -> Printf.sprintf "\"%s\" := %s" key (p v)) xs
  in
  match xs with
  | [] -> "∅"
  | _ ->
      let s = String.concat ";" xs in
      Printf.sprintf "{[ %s ]}" s

let rec cmd_pretty = function
  | SkipC -> "SkipC"
  | SeqC { fstc; sndc } ->
      Printf.sprintf "SeqC (%s) (%s)" (cmd_pretty fstc) (cmd_pretty sndc)
  | LetC { lhs; e } -> Printf.sprintf "LetC \"%s\" (%s)" lhs (expr_pretty e)
  | IfC { cond; thn; els } ->
      Printf.sprintf "IfC (%s) (%s) (%s)" (expr_pretty cond) (cmd_pretty thn)
        (cmd_pretty els)
  | GetC { lhs; recv; name } ->
      Printf.sprintf "GetC \"%s\" (%s) \"%s\"" lhs (expr_pretty recv) name
  | SetC { recv; name; rhs } ->
      Printf.sprintf "SetC (%s) \"%s\" (%s)" (expr_pretty recv) name
        (expr_pretty rhs)
  | ErrorC -> "ErrorC"
  | CallC { lhs; recv; name; args } ->
      let args = pretty_map expr_pretty args in
      Printf.sprintf "CallC \"%s\" (%s) \"%s\" %s" lhs (expr_pretty recv) name
        args
  | NewC { lhs; name; ty_args; args } ->
      let args = pretty_map expr_pretty args in
      let ty_args =
        match ty_args with
        | [] -> "None"
        | _ ->
            let l = List.map lang_ty_pretty ty_args in
            let s = String.concat ";" l in
            Printf.sprintf "(Some [ %s ])" s
      in
      Printf.sprintf "NewC \"%s\" \"%s\" %s %s" lhs name ty_args args
  | RuntimeCheckC { v; rc; thn; els } ->
      ignore v;
      ignore rc;
      ignore thn;
      ignore els;
      failwith "RTC"

let methodDef_pretty cname { name; args; return_type; body; return } =
  let args = pretty_map lang_ty_pretty args in
  let l =
    [
      "{|";
      Printf.sprintf "  methodargs := %s;" args;
      Printf.sprintf "  methodrettype := %s;" (lang_ty_pretty return_type);
      Printf.sprintf "  methodbody := %s;" (cmd_pretty body);
      Printf.sprintf "  methodret := %s;" (expr_pretty return);
      Printf.sprintf "  methodvisibility := Public;";
      (* TODO *)
      "|}";
    ]
  in
  let s = String.concat "\n" l in
  Printf.sprintf "Definition %s_%s := %s." cname name s

let classDef_pretty { name; generics = _; constraints; super; fields; methods }
    =
  let cs =
    List.flatten
    @@ List.map
         (fun (var, l, r) ->
           let l = lang_ty_pretty l in
           let r = lang_ty_pretty r in
           match var with
           | Eq -> [ (l, r); (r, l) ]
           | As -> [ (l, r) ]
           | Super -> [ (r, l) ])
         constraints
  in
  let cs = List.map (fun (l, r) -> Printf.sprintf "(%s, %s)" l r) cs in
  let cs = Printf.sprintf "[%s]" (String.concat ";" cs) in
  let super =
    match super with
    | None -> "None"
    | Some (t, targs) ->
        let l = List.map lang_ty_pretty targs in
        let s = String.concat ";" l in
        Printf.sprintf "Some(\"%s\", [%s])" t s
  in
  let fields =
    List.map
      (fun (vis, ty, name) ->
        Printf.sprintf "\"%s\" := (%s, %s)" name (show_visibility vis)
          (lang_ty_pretty ty))
      fields
  in
  let fields =
    match fields with
    | [] -> "∅"
    | _ ->
        let s = String.concat ";" fields in
        Printf.sprintf "{[%s]}" s
  in
  let l =
    [
      "{|";
      Printf.sprintf "  superclass := %s;" super;
      Printf.sprintf "  generics := [];";
      Printf.sprintf "  constraints := %s;" cs;
      Printf.sprintf "  classfields := %s;" fields;
      Printf.sprintf "  classmethods := ∅;";
      "|}";
    ]
  in
  let s = String.concat "\n" l in
  let cls = Printf.sprintf "Definition %s := %s." name s in
  let mthds = List.map (fun mdef -> methodDef_pretty name mdef) methods in
  let mthds = String.concat "\n\n" mthds in
  Printf.sprintf "%s\n\n%s" mthds cls

let program_pretty l =
  let prelude = [ "Definition arraykey := UnionT IntT BoolT." ] in
  let l = List.map classDef_pretty l in
  String.concat "\n\n" (List.append prelude l)
