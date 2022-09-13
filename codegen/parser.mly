%{
  (* open Lexing *)
  module L = Location

  type elt_kind =
    | Field of (Ast.visibility * string * Ast.lang_ty)
    | Method of Ast.methodDef

  let to_class elts =
    let open Ast in
    List.fold_left (fun (facc, macc) kind ->
        match kind with
        | Field (vis, name, ty) ->
          (SMap.add name (vis, ty) facc, macc)
        | Method mdef ->
          (facc, SMap.add mdef.name mdef macc))
      (SMap.empty, SMap.empty) elts

  let to_map l =
    let open Ast in
    List.fold_left (fun acc (name, value) ->
        SMap.add name value acc)
      SMap.empty l

  let rec to_sequence l =
    let open Ast in
    match l with
    | [] -> SkipC
    | [ c ] -> c
    | c0 :: c1 :: [] ->
      SeqC { fstc = c0; sndc = c1 }
    | c0 :: c1 :: rest ->
      let c = to_sequence rest in
      SeqC { fstc = c0; sndc = SeqC { fstc = c1; sndc = c } }
%}

%token ErrorCmd
%token This
%token Is
%token New
%token Let
%token Function
%token Return
%token Class
%token Extends
%token Where
%token As
%token Super
%token Public
%token Private
%token If
%token Then
%token Else
%token True
%token False
%token Comma
%token Colon
%token Semi
%token LPar
%token RPar
%token LBrace
%token RBrace
%token Plus
%token Minus
%token Times
%token Div
%token Eq
%token Not
%token Lt
%token Gt
%token Upcast
%token Ampersand
%token Pipe
%token Hash
%token Arrow
%token Bool
%token IntT
%token Null
%token Nonnull
%token Mixed
%token Nothing
%token Dynamic
%token Eof

%token <int> Int
(* %token <string> String *)
%token <string> Id

%right Else
%left Pipe
%left Ampersand
%nonassoc Eq Gt Lt
%left Plus Minus
%left Times Div
%left Not
(* %left Hash *)

%start <Ast.program> prog

%%

symbol :
    | x = Id { x }

prog :
  | cdefs = list(classDef) Eof { cdefs }
  | error { Errors.syntax_error (L.mk $startpos $endpos) "" }

ty_args :
  | Lt targs = separated_list(Comma, ty) Gt { targs }

ty :
  | IntT { Ast.IntT }
  | Bool { Ast.BoolT }
  | Null { Ast.NullT }
  | Nonnull { Ast.NonNullT }
  | Mixed { Ast.MixedT }
  | Nothing { Ast.NothingT }
  | Dynamic { Ast.DynamicT }
  | Hash t = symbol { Ast.GenT t }
  | t0 = ty Pipe t1 = ty { Ast.UnionT (t0, t1) }
  | t0 = ty Ampersand t1 = ty { Ast.InterT (t0, t1) }
  | LPar t = ty RPar { t }
  | Class t = symbol targs = ty_args { Ast.ClassT { name = t; tyargs = targs }
                                     }
exp :
    | var = symbol { Ast.VarE var }
    | n = Int { Ast.IntE n }
    | _true = True { Ast.BoolE true }
    | _false = False { Ast.BoolE false }
    | Not e = exp {
        Ast.UniOpE { op = NotO;  e = e }
      } %prec Not
    | e1 = exp o = op e2 = exp { Ast.BinOpE {op = o; lhs = e1; rhs = e2} }
    (* | s = String { Ast.String s } *)
    | Null { Ast.NullE }
    | This { Ast.ThisE }
    | Upcast LPar e = exp Comma t = ty RPar { Ast.UpcastE { e = e; ty = t } }

arg :
    | name = symbol Eq e = exp { (name, e) }

rtc :
    | Is IntT { Ast.RCInt }
    | Is Bool { Ast.RCBool }
    | Is Null { Ast.RCNull }
    | Is Nonnull { Ast.RCNonNull }
    | Is tag = symbol { Ast.RCTag tag }

cmd :
    | LBrace seq = separated_list(Semi, cmd) RBrace {
        to_sequence seq
    }
    | Let v = symbol Eq e = exp { Ast.LetC { lhs = v; e = e } }
    | If cond = exp Then if_true = cmd {
        Ast.IfC {cond = cond; thn = if_true; els = Ast.SkipC }
    } %prec Else
    | If cond = exp Then if_true = cmd Else if_false = cmd {
        Ast.IfC { cond = cond; thn = if_true; els = if_false }
    }
    | Let lhs = symbol Eq recv = exp Arrow mname = symbol LPar args = separated_list(Comma, arg) RPar {
        let args = to_map args in
        Ast.CallC { lhs = lhs; recv = recv; name = mname; args = args }
    }
    | Let lhs = symbol Eq New t = symbol targs = ty_args LPar args =
      separated_list(Comma, arg) RPar {
        let args = to_map args in
        Ast.NewC { lhs = lhs; name = t; ty_args = targs; args = args }
      }
    | Let lhs = symbol Eq recv = exp Arrow field = symbol {
        Ast.GetC { lhs = lhs; recv = recv; name = field }
      }
    | recv = exp Arrow field = symbol Eq rhs = exp {
        Ast.SetC { recv = recv; name = field; rhs = rhs }
    }
    | If v = symbol check = rtc Then if_true = cmd {
        Ast.RuntimeCheckC { v = v; rc = check; thn = if_true; els = SkipC }
      } %prec Else
    | If v = symbol check = rtc Then if_true = cmd Else if_false = cmd {
        Ast.RuntimeCheckC { v = v; rc = check; thn = if_true; els = if_false }
      }
    | ErrorCmd { Ast.ErrorC }

%inline op :
    | Plus { Ast.PlusO }
    | Minus { Ast.MinusO }
    | Times { Ast.TimesO }
    | Div { Ast.DivO }
    | Eq { Ast.EqO }
    | Gt { Ast.GtO }
    | Lt { Ast.LtO }

farg :
    | t = ty name = symbol { (name, t) }

methodDef :
    | Function mname = symbol LPar args = separated_list(Comma, farg) RPar
        Colon retty = ty body = cmd Return ret = exp {
        Ast.{name = mname; args = to_map args; return_type = retty;
             body = body; return = ret }
      }

extends_clause :
  | Extends tag = symbol targs = ty_args { (tag, targs) }

%inline constr_op :
  | Eq { Ast.Eq }
  | As { Ast.As }
  | Super { Ast.Super }

constr:
  | l = ty op = constr_op r = ty { (op, l , r) }


where_clause :
  | Where cs = separated_list(Comma, constr) { cs }

visibility :
  | Public { Ast.Public }
  | Private { Ast.Private }

class_elt :
  | vis = visibility t = ty name = symbol { Field (vis, name, t) }
  | mdef = methodDef { Method mdef }


classDef :
    | Class cname = symbol ext = option(extends_clause)
        where = option(where_clause) LBrace
        elts = separated_list(Semi, class_elt)
        RBrace {
        let (fields, methods) = to_class elts in
        let where = match where with None -> []
                                   | Some l -> l in
        Ast.{ name = cname;
              generics = []; (* TODO *)
              constraints = where;
              super = ext;
              fields = fields;
              methods = methods;
            }
      }
