(*
 * Copyright (c) Meta Platforms, Inc. and affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 *)

open Ast
open Printf

let rec lang_ty_pretty = function
  | IntT -> "IntT"
  | BoolT -> "BoolT"
  | NothingT -> "NothingT"
  | MixedT -> "MixedT"
  | ClassT { name; tyargs } ->
      let l = List.map lang_ty_pretty tyargs in
      let s = String.concat ";" l in
      sprintf "(ClassT true \"%s\" ([%s]))" name s
  | NullT -> "NullT"
  | NonNullT -> "NonNullT"
  | UnionT (s, t) ->
      sprintf "(UnionT (%s) (%s))" (lang_ty_pretty s) (lang_ty_pretty t)
  | InterT (s, t) ->
      sprintf "(InterT (%s) (%s))" (lang_ty_pretty s) (lang_ty_pretty t)
  | GenT _ -> (* TODO: debruijn ? *) "(GenT XXX)"
  | DynamicT -> "DynamicT"
  | SupportDynT -> "SupportDynT"

let rec expr_pretty = function
  | IntE n -> sprintf "(IntE %d)" n
  | BoolE b -> sprintf "(BoolE %b)" b
  | NullE -> "NullE"
  | BinOpE { op; lhs; rhs } ->
      sprintf "(BinOpE %s (%s) (%s))" (show_binop op) (expr_pretty lhs)
        (expr_pretty rhs)
  | UniOpE { op; e } ->
      sprintf "(UniOpE %s (%s))" (show_uniop op) (expr_pretty e)
  | VarE s -> sprintf "(VarE %s)" s
  | ThisE -> "ThisE"
  | UpcastE { e; ty } ->
      sprintf "(Upcast (%s) (%s))" (expr_pretty e) (lang_ty_pretty ty)

let runtime_check_pretty = function
  | RCTag s -> sprintf "(RCTag \"%s\")" s
  | RCInt -> "RCInt"
  | RCBool -> "RCBool"
  | RCNull -> "RCNull"
  | RCNonNull -> "RCNonNull"

let pretty_map p xs =
  let xs = List.map (fun (key, v) -> sprintf "\"%s\" := %s" key (p v)) xs in
  match xs with
  | [] -> "∅"
  | _ ->
      let s = String.concat ";" xs in
      sprintf "{[ %s ]}" s

let rec cmd_pretty = function
  | SkipC -> "SkipC"
  | SeqC { fstc; sndc } ->
      sprintf "(SeqC (%s) (%s))" (cmd_pretty fstc) (cmd_pretty sndc)
  | LetC { lhs; e } -> sprintf "(LetC \"%s\" (%s))" lhs (expr_pretty e)
  | IfC { cond; thn; els } ->
      sprintf "(IfC (%s) (%s) (%s))" (expr_pretty cond) (cmd_pretty thn)
        (cmd_pretty els)
  | GetC { lhs; recv; name } ->
      sprintf "(GetC \"%s\" (%s) \"%s\")" lhs (expr_pretty recv) name
  | SetC { recv; name; rhs } ->
      sprintf "(SetC (%s) \"%s\" (%s))" (expr_pretty recv) name
        (expr_pretty rhs)
  | ErrorC -> "ErrorC"
  | CallC { lhs; recv; name; args } ->
      let args = pretty_map expr_pretty args in
      sprintf "(CallC \"%s\" (%s) \"%s\" %s)" lhs (expr_pretty recv) name args
  | NewC { lhs; name; ty_args; args } ->
      let args = pretty_map expr_pretty args in
      let ty_args =
        match ty_args with
        | [] -> "None"
        | _ ->
            let l = List.map lang_ty_pretty ty_args in
            let s = String.concat ";" l in
            sprintf "(Some [ %s ])" s
      in
      sprintf "(NewC \"%s\" \"%s\" %s %s)" lhs name ty_args args
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
      sprintf "  methodargs := %s;" args;
      sprintf "  methodrettype := %s;" (lang_ty_pretty return_type);
      sprintf "  methodbody := %s;" (cmd_pretty body);
      sprintf "  methodret := %s;" (expr_pretty return);
      sprintf "  methodvisibility := Public;";
      (* TODO *)
      "|}";
    ]
  in
  let s = String.concat "\n" l in
  sprintf "Definition %s_%s := %s." cname name s

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
  let cs = List.map (fun (l, r) -> sprintf "(%s, %s)" l r) cs in
  let cs = sprintf "[%s]" (String.concat ";" cs) in
  let super =
    match super with
    | None -> "None"
    | Some (t, targs) ->
        let l = List.map lang_ty_pretty targs in
        let s = String.concat ";" l in
        sprintf "Some(\"%s\", [%s])" t s
  in
  let fields =
    List.map
      (fun (vis, ty, name) ->
        sprintf "\"%s\" := (%s, %s)" name (show_visibility vis)
          (lang_ty_pretty ty))
      fields
  in
  let fields =
    match fields with
    | [] -> "∅"
    | _ ->
        let s = String.concat ";" fields in
        sprintf "{[%s]}" s
  in
  let l =
    [
      "{|";
      sprintf "  superclass := %s;" super;
      sprintf "  generics := [];";
      sprintf "  constraints := %s;" cs;
      sprintf "  classfields := %s;" fields;
      sprintf "  classmethods := ∅;";
      "|}";
    ]
  in
  let s = String.concat "\n" l in
  let cls = sprintf "Definition %s := %s." name s in
  let mthds = List.map (fun mdef -> methodDef_pretty name mdef) methods in
  let mthds = String.concat "\n\n" mthds in
  sprintf "%s\n\n%s" mthds cls

let program_pretty l =
  let prelude = [ "Definition arraykey := UnionT IntT BoolT." ] in
  let l = List.map classDef_pretty l in
  String.concat "\n\n" (List.append prelude l)
