open Cil 
open Pretty
open Tututil

module I64 = Int64
module L  = List     
module E  = Errormsg 
module IH = Inthash  
module DF = Dataflow 
module HT = Hashtbl

exception InvalidValue
exception UnsupportedOperation of string
exception EmptyList
exception CouldNotFindLoopTerminator
exception DoesNotContainStatement
exception ProcessingUnknown

type expression = 
  | Constant of int 
  | Variable of varinfo
  | Addition of expression * expression
  | Multiplication of int * expression
  | UnknownExpr

type constr =
  | Top 
  | AND of constr * constr
  | NOT of constr
  | OR of constr * constr
  | LEQ of expression
  | Exists of string * constr
  | Forall of string * constr
  | Bottom
  | UnknownConstr

let debug = ref false
let lineTable = HT.create 100
let targetLine = ref (-1)
let qcnt = ref 0
let quants: (string list) ref = ref []
let quant_atleast_once: bool ref = ref false

let rec string_of_expression (ex : expression) : string = 
  match ex with
  | Constant(i) -> (string_of_int i)
  | Variable(id) -> (id.vname)
  | Addition(exp1, exp2) ->  "( "^((string_of_expression exp1)^" ) + ( "^(string_of_expression exp2))^" )"
  | Multiplication(i, exp) -> "( "^((string_of_int i)^" ) * ( "^(string_of_expression exp))^" )"
  | UnknownExpr -> "UNKNOWN" 

let rec string_of_constr (c : constr) : string = 
  match c with
  | Top -> "Top"
  | AND(c1, c2) -> ("("^(string_of_constr c1)^") AND ("^(string_of_constr c2)^")")
  | NOT(c1) -> ("NOT ("^(string_of_constr c1)^")")
  | OR(c1, c2) -> ("("^(string_of_constr c1)^") OR ("^(string_of_constr c2)^")")
  | LEQ(e) -> ("("^(string_of_expression e)^") <= 0")
  | Exists(x, c) -> ("(exists (("^x^" Int)) "^(string_of_constr c)^")")
  | Forall(x, c) -> ("(forall (("^x^" Int)) "^(string_of_constr c)^")")
  | Bottom -> "Bottom" 
  | UnknownConstr -> "UConstr"

let rec z3_string_of_expression (ex : expression) : string =
  match ex with
  | Constant(i) -> if i >= 0 then (string_of_int i) else "(- "^(string_of_int (-1*i))^")"
  | Variable(id) -> id.vname
  | Addition(exp1, exp2) ->  "(+ "^((z3_string_of_expression exp1)^" "^(z3_string_of_expression exp2))^" )"
  | Multiplication(i, exp) -> "(* "^((if i >= 0 then (string_of_int i) else "(- "^(string_of_int (-1*i) )^")")^" "^(z3_string_of_expression exp))^" )"
  | UnknownExpr -> "UNKNOWN"

let rec z3_string_of_constr (c : constr) : string =
  match c with
  | Top -> "true"
  | AND(c1, c2) -> ("(and "^(z3_string_of_constr c1)^" "^(z3_string_of_constr c2)^")")
  | NOT(c1) -> ("(not "^(z3_string_of_constr c1)^")")
  | OR(c1, c2) -> ("(or "^(z3_string_of_constr c1)^" "^(z3_string_of_constr c2)^")")
  | LEQ(e) -> ("(<= "^(z3_string_of_expression e)^" 0)")
  | Exists(x, c) -> (z3_string_of_constr c)
  | Forall(x, c) -> (z3_string_of_constr c)
  | Bottom -> "false"
  | UnknownConstr -> "UConstr"

let rec expression_equals (e1 : expression) (e2 : expression) : bool =
  match e1, e2 with
  | Constant(i1), Constant(i2) -> i1 = i2
  | Variable(v1), Variable(v2) -> v1.vname = v2.vname
  | Addition(e11, e12), Addition(e21, e22) -> ( (expression_equals e11 e21) && (expression_equals e12 e22) )
  | Multiplication(i1, e1), Multiplication(i2, e2) -> ( (i1 = i2) && (expression_equals e1 e2) )
  | _ -> false

let rec constr_equals (c1 : constr) (c2 : constr) : bool =
  match c1, c2 with
  | AND(c11, c12), AND(c21, c22) -> ( (constr_equals c11 c21) && (constr_equals c12 c22) )
  | NOT(c11), NOT(c21) -> (constr_equals c11 c21) 
  | OR(c11, c12), OR(c21, c22) -> ( (constr_equals c11 c21) && (constr_equals c21 c22) )
  | LEQ(e1), LEQ(e2) -> (expression_equals e1 e2)
  | Exists(x1,c1), Exists(x2,c2) -> ((x1==x2) && (constr_equals c1 c2))
  | Forall(x1,c1), Exists(x2,c2) -> ((x1==x2) && (constr_equals c1 c2))
  | Top, Top -> true
  | Bottom, Bottom -> true
  | _ -> false

type varmap = int * (varinfo * constr)
(*
type direction = Increasing | Decreasing
type testDirection = IsIncreasing | IsDecreasing | Unknown
type loopData = int * (varmap list * direction )
type loopmap = int * loopData 
let pastLoops = ref []
let loop_count (l : loopData) : int = (fst l)
let loop_old (l : loopData) : varmap list = l |> snd |> fst
let loop_direction (l : loopData) : direction = l |> snd |> snd  
*)
let pastLoops = ref []

let id_of_vm   (vm : varmap) : int     = fst vm
let vi_of_vm   (vm : varmap) : varinfo = vm |> snd |> fst
let constr_of_vm (vm : varmap) : constr  = vm |> snd |> snd

let rec z3_gather_vars (vml : varmap list) : string list =
  match vml with
  | h::t -> (vi_of_vm h).vname :: (z3_gather_vars t)
  | [] -> [ ]
 
let string_of_varmap (vm : varmap) : string =
  "("^(vm |> constr_of_vm |> string_of_constr)^")"

let string_of_varmap_list (vml : varmap list) : string =
  vml
  |> L.map string_of_varmap
  |> String.concat "\n AND "

let rec generate_decls_for_vars (l : string list) : string =
  match l with
  | h::t -> "(declare-const "^h^" Int)\n"^(generate_decls_for_vars t)
  | [] -> ""

let rec z3_string_of_varmap_list_wo_decls (vml : varmap list) : string =
  match vml with
  | [ x ] -> (z3_string_of_constr (constr_of_vm x))
  | [ ] -> ""
  | h::t -> "(and "^(z3_string_of_constr (constr_of_vm h))^" "^(z3_string_of_varmap_list_wo_decls t)^" )"
(*
let stupid_while (sl : string list) (head: string): string list =
  let count = ref 0 in
  while(!count < !qcnt) do
  sl = head::sl;
  count := !count + 1;
  done
let rec z3_string_of_quants (vml : varmap list): string list =
  match vml with
  (* Print (x Int) (y Int) ...	 *)
  | h::t -> 
  let temp = ("("^((vi_of_vm h).vname)^" Int)")::(z3_string_of_quants t) in
  temp
  | _ -> []
*)

let rec z3_print_list_string (sl: string list) : string =
  match sl with
  | h::t -> ("("^h^" Int)")^(z3_print_list_string t)
  | _ -> ""

let z3_string_of_varmap_list (vml : varmap list) : string =
    let varnames = z3_gather_vars (vml : varmap list) in
    (generate_decls_for_vars varnames)^"\n(elim-quantifiers (exists ("^(z3_print_list_string !quants)^")"^(z3_string_of_varmap_list_wo_decls vml)^"))"

let varmap_list_pretty () (vml : varmap list) =
  vml |> string_of_varmap_list |> text

let string_of_binop (op : binop) : string =
  match op with 
  | Lt -> "<"
  | Gt -> ">"
  | Le -> "<="
  | Ge -> ">="
  | _ -> ""

let string_of_unop (op : unop) : string =
  match op with
  | LNot -> "!"
  | _ -> ""

let rec string_of_exp (e : exp) : string =
  match e with
  | BinOp(op, lhs, rhs, resultType) -> "BinaryOp"^(string_of_binop op)^"("^(string_of_exp lhs)^", "^(string_of_exp rhs)^")"
  | Const(const) -> "Constant"
  | UnOp(op, e, resultType) -> ("UnaryOp"^(string_of_unop op)^"("^(string_of_exp e)^")")
  | Lval(l) -> "LVal"
  | Question(cond, onTrue, onFalse, resultType) -> "Question"
  | _ -> "Expression"

let varmap_equal (vm1 : varmap) (vm2 : varmap) : bool =
  (id_of_vm vm1) = (id_of_vm vm2) &&
  (constr_equals (constr_of_vm vm1) (constr_of_vm vm2))

let varmap_list_equal (vml1 : varmap list) (vml2 : varmap list) : bool =
  let sort = L.sort (fun (id1,_) (id2,_) -> compare id1 id2) in
  list_equal varmap_equal (sort vml1) (sort vml2)

let merge_constr (c1 : constr) (c2 : constr) : constr =
  OR(c1, c2)

let rec constr_combine (c1 : constr) (c2 : constr) : constr =
  AND(c1, c2)
  
let varmap_combine (vm1 : varmap) (vm2 : varmap) : varmap option =
  match vm1, vm2 with
  | (id1, _), (id2, _) when id1 <> id2 -> None
  | (id1, (vi1, k1)), (_,(_,k2)) -> Some(id1,(vi1,constr_combine k1 k2))

let gen_string (id: string) (add: bool) : string =
  E.log "gen_string called: %s\n" id;
  let temp = id^(string_of_int !qcnt) in
  if(add) then
  begin
  quants := temp::(!quants);
  temp
  end
  else
  temp

let rec expr_prime_vi (e: expression) (vi: varinfo) : expression =
  match e with
  | Variable(id) ->
    if(id.vname==vi.vname) then
    begin
     let temp_name = (gen_string id.vname false) in
     let vi_prime = (Cil.copyVarinfo id temp_name) in
     Variable(vi_prime)
    end
    else
	Variable(id)
  | Addition(e1, e2) -> Addition((expr_prime_vi e1 vi), (expr_prime_vi e2 vi))
  | Multiplication(i, e) -> Multiplication(i, (expr_prime_vi e vi))
  | _ -> e

let rec constr_prime_vi (c: constr) (vi: varinfo) : constr =
  match c with
  | Exists(x, c) -> Exists(x, (constr_prime_vi c vi))
  | Forall(x, c) -> Forall(x, (constr_prime_vi c vi))
  | AND(c1, c2) -> AND((constr_prime_vi c1 vi),(constr_prime_vi c2 vi))
  | OR(c1, c2) -> OR((constr_prime_vi c1 vi),(constr_prime_vi c2 vi))
  | NOT(c) -> NOT((constr_prime_vi c vi))
  | LEQ(expr) -> LEQ((expr_prime_vi expr vi))
  | _ -> c

let varmap_prime (vm: varmap) (vi: varinfo) : varmap =
  match vm with
  | (id, (vinf, constr)) ->
  let cn = (constr_prime_vi constr vi) in
  (id, (vinf, cn))

let varmap_list_combine_one (vml : varmap list) (vm : varmap) : varmap list =
  let id = id_of_vm vm in
  if L.mem_assoc id vml then
    let vm' = (id, L.assoc id vml) in
    let vm'' = forceOption (varmap_combine vm vm') in
    vm'' :: (L.remove_assoc (id_of_vm vm) vml)
  else vm :: vml
(*
let varmap_list_combine_one_primed (vml : varmap list) (vm : varmap) : varmap list =
  let id = id_of_vm vm in
  if L.mem_assoc id vml then
    let vm' = (id, L.assoc id vml) in
    let vm' = (varmap_prime vm') in
    let vm'' = forceOption (varmap_combine vm vm') in
    vm'' :: (L.remove_assoc (id_of_vm vm) vml)
  else vm :: vml
*)
let varmap_list_combine (vml1 : varmap list) (vml2 : varmap list) : varmap list =
  L.fold_left varmap_list_combine_one vml1 vml2

let varmap_list_replace (vml : varmap list) (vm : varmap) : varmap list =
  vm :: (L.remove_assoc (id_of_vm vm) vml)

(*
let loopmap_list_replace (lml : loopmap list) (lm : loopmap) : loopmap list =
  lm :: (L.remove_assoc (fst lm) lml)
*)

let rec apply_neg_to_expression (e : expression) : expression = 
  match e with 
  | Constant(i) -> Constant(-1 * i)
  | Variable(v) -> Multiplication(-1, Variable(v))
  | Addition(e1, e2) -> Addition( apply_neg_to_expression e1, apply_neg_to_expression e2)
  | Multiplication(i, e) -> Multiplication(-1 * i, e)
  | UnknownExpr -> raise ProcessingUnknown

let rec apply_neg_to_constr (c : constr) : constr =
  match c with
  | Top -> Bottom
  | AND(c1, c2) -> AND( (apply_neg_to_constr c1), (apply_neg_to_constr c2) )
  | NOT(c1) -> NOT( (apply_neg_to_constr c1) )
  | OR(c1, c2) -> OR( (apply_neg_to_constr c1), (apply_neg_to_constr c2) )
  | LEQ(e) -> LEQ( (apply_neg_to_expression e) )
  | Exists(x, c) -> Forall(x, (apply_neg_to_constr c))
  | Forall(x, c) -> Exists(x, (apply_neg_to_constr c)) 
  | Bottom -> Top
  | UnknownConstr -> raise ProcessingUnknown

let rec expression_of_exp (vml : varmap list) (e : exp) : expression =
  match e with
  | Const(CInt64(i, _, _)) -> Constant( (I64.to_int i))
  | Lval(Var vi, NoOffset) -> Variable(vi) 
  | SizeOf _ | SizeOfE _ | SizeOfStr _ | AlignOf _ | AlignOfE _ ->
    e |> constFold true |> expression_of_exp vml 
  | UnOp(uo, e, t) -> expression_of_unop vml uo e
  | BinOp(bo, e1, e2, t) -> expression_of_binop vml bo e1 e2
  | CastE(t, e) -> expression_of_exp vml e
  | _ -> UnknownExpr

and expression_of_unop (vml : varmap list) (u : unop) (e : exp) : expression =
  match u with
  | Neg  -> e |> expression_of_exp vml |> apply_neg_to_expression
  | _ -> UnknownExpr

and expression_of_binop (vml : varmap list) (b : binop) (e1 : exp) (e2 : exp) : expression =
  let k1, k2 = expression_of_exp vml e1 , expression_of_exp vml e2 in
  match b with
  | PlusA -> Addition(k1, k2)
  | MinusA -> Addition(k1, Multiplication(-1, k2))
  | _ -> UnknownExpr 

let rec replace_prime_vml (vml: varmap list) (vi: varinfo) : varmap list =
  match vml with
  | h::t -> (varmap_prime h vi)::(replace_prime_vml t vi)
  | [ x ] -> [varmap_prime x vi]
  | _ -> vml

let rec replace_prime (e: exp) (vi : varinfo) : exp =

  match e with
  | Lval(Var vin, NoOffset) ->
(*
  if(not(!quant_atleast_once)) then
  begin
    (gen_string vi.vname true);
    quant_atleast_once := true;
  end
*)
   (match vin.vname with
    | x -> 
  	if(x==vi.vname) then
	begin
	let vi_prime = (Cil.copyVarinfo vi (gen_string x false)) in
	Lval(Var vi_prime, NoOffset)
	end
	else
	Lval(Var vin, NoOffset)
    )
(*
    if(not(!quant_atleast_once)) then
    begin
      let temp_name = (gen_string vi.vname) in
      quant_atleast_once := true;
    end
    
    if(vin.vname==vi.vname) then
    begin
     let vi_prime = (Cil.copyVarinfo vi temp_name) in
     Lval(Var vi_prime, NoOffset)
    end
    else
     Lval(Var vin, NoOffset)
*)
  | UnOp(uo, exp, t) -> 
    let new_exp = (replace_prime exp vi) in
	UnOp(uo,new_exp,t)
  | BinOp(bo, e1, e2, t) ->
    let new_exp1 = (replace_prime e1 vi) in let new_exp2 = (replace_prime e2 vi) in
	BinOp(bo,new_exp1,new_exp2,t)
  | _ -> e  
 
let constr_of_exp (vml : varmap list) (e : exp) (vi : varinfo) : constr =
    qcnt := !qcnt + 1;
    (gen_string vi.vname true);
    E.log "expression is: %a\n" (docList ~sep:line (d_exp ())) [e];
    let cil_exp_old = (replace_prime e vi) in
    let inner_exp = (expression_of_exp vml cil_exp_old) in
    Exists("", LEQ( Addition( Variable(vi), Multiplication(-1, inner_exp ))))
(*
  let inner_exp = (expression_of_exp vml e) in
    AND( LEQ( Addition( Variable(vi), Multiplication(-1, inner_exp ) ) ), NOT( LEQ( Addition( Variable(vi), Multiplication( -1, Addition( Constant(-1), inner_exp ) ) ) ) ) )
*)

let constr_of_binop (vml : varmap list) (b : binop) (rhs : exp) (vi : varinfo) : constr =
  match b with
  | Le -> LEQ( Addition( Variable(vi), Multiplication(-1, (expression_of_exp vml rhs) ) ) )
  | _ -> raise (UnsupportedOperation((string_of_exp rhs)))

let varmap_list_kill (vml : varmap list) : varmap list =
  L.map (fun (vid, (vi, k)) ->
    if vi.vaddrof then (vid, (vi, Top)) else (vid, (vi, k)))
  vml

let varmap_list_handle_inst (i : instr) (vml : varmap list) : varmap list =
  match i with
  | Set((Var vi, NoOffset), e, loc)
      when not(vi.vglob) && (isIntegralType vi.vtype) ->
    (HT.replace lineTable loc.line vml);
    (* This returns the varmap list after overwriting constraints for var	*)
    (* Instead, it should string constraints together				*)
    let k = constr_of_exp vml e vi in
(*
    let id = vi.vid in
    if L.mem_assoc id vml then
      let vm' = (id, L.assoc id vml) in
      let k = And(k,(constr_of_vm vm')) in 
      let vm' = (varmap_prime vm')
    else
      let vm' = (id, (vi, k))
*)
(*    (varmap_list_pretty vml); *)
    let result = (replace_prime_vml vml vi) in
(*    (varmap_list_pretty result); *)
    let result = varmap_list_combine_one result (vi.vid,(vi,k)) in 
    result
(*    let result = varmap_list_replace vml (vi.vid,(vi,k)) in result *)
  | Set((Mem _, _), _, _)
  | Call _ -> varmap_list_kill vml 
  | _ -> vml

let rec gather_varids_in (e : exp) : int list = 
  match e with
  | BinOp(op, lhs, rhs, resultType) -> (L.append (gather_varids_in lhs ) (gather_varids_in rhs ) )
  | UnOp(op, ex, resultType) -> (gather_varids_in ex )
  | Lval(lv) -> (match (fst lv) with
                   | Var(info) -> [ info.vid ]
                   | _ -> [] )
  | Const(c) -> []
  | _ -> []

let string_of_stmtkind (sk : stmtkind) : string = 
  match sk with
    | Break(loc) -> "Break"
    | If(e, b1, b2, loc) -> "If"
    | Instr(l) -> "Insn"
    | Goto(r, l) -> "Goto"
    | Continue(loc) -> "Continue"
    | Loop(bl, loc, s1, s2) -> "Loop"
    | Block(bl) -> "Block"
    | Return(e, loc) -> "Return"
    | _ -> "UnknownStatementKind"

let process_guard_binop (op : binop) (lhs : exp) (rhs : exp) (ll : varmap list) : varmap list =
    match op with
      | Le -> (
        match lhs with
          | Lval(lv) -> (
            match (fst lv) with
             | Var(info) -> (varmap_list_replace ll (info.vid, ( (fst (L.assoc info.vid ll)), (match (snd (L.assoc info.vid ll)) with | UnknownConstr -> ( constr_of_binop ll op rhs info) | _ -> AND( (snd (L.assoc info.vid ll)), ( constr_of_binop ll op rhs info) ) ) ) ) )
             | _ -> raise (UnsupportedOperation ("BBBB")) )
          | _ -> raise (UnsupportedOperation ("CCCC")) )
      | _ -> raise (UnsupportedOperation ("DDDD") )

let rec varmap_list_handle_stmt (s : stmt) (vml : varmap list) : varmap list =
  match s.skind with
  | If(cond, tb, fb, loc) ->
    E.log "In varmap_handle_stmt: If\n";
    (match cond with
      | BinOp(op, lhs, rhs, resultType) ->
	E.log "In varmap_handle_stmt: If->Binop\n";
	(match op with
	| Le -> 
        (process_guard_binop op lhs rhs vml)
	| _ -> raise (UnsupportedOperation ("binop not le")))
      | UnOp(op, e, resultType) ->
	E.log "In varmap_handle_stmt: If->Unop\n";
        (match op with
          | LNot -> (
            match e with
              | BinOp(op, lhs, rhs, resultType) -> 
                 (process_guard_binop op lhs rhs vml)
              | _ -> raise (UnsupportedOperation ("GGGG")) )
          | _ -> raise (UnsupportedOperation ("FFFF")) )
      | _ -> raise (UnsupportedOperation (string_of_exp cond) ))
  | _ -> vml
 
let rec varmap_list_handle_bstmts (bstmts : stmt list) (vml : varmap list) : varmap list =
  match bstmts with
  | h::t -> 
    let temp_vml = (varmap_list_handle_stmt h vml) in
	(varmap_list_handle_bstmts t temp_vml)

let rec find_int_in_list (l : int list) (v : int) : bool =
  match l with
  | h::t -> if h = v then true else (find_int_in_list t v)
  | [] -> false

module OddEvenDF = struct
  let name = "OddEven"
  let debug = debug
  type t = varmap list
  let copy vml = vml
  let stmtStartData = IH.create 64
  let pretty = varmap_list_pretty
  let computeFirstPredecessor stm vml = vml
  let combinePredecessors (s : stmt) ~(old : t) (ll : t) =
    if varmap_list_equal old ll then None else
    Some(varmap_list_combine old ll)
  let doInstr (i : instr) (ll : t) =
    let action = varmap_list_handle_inst i in
    DF.Post action
  let doStmt (stm : stmt) (ll : t) = 
(*    let action = (varmap_list_handle_stmt stm ll) in
    DF.Post action *)
    DF.SDefault
(*    DF.SUse (varmap_list_handle_stmt stm ll) *)

  let doGuard ( c : exp ) (ll : varmap list) =
(*     E.log "%a\n" pretty ll; *)
     E.log "%a\n" (docList ~sep:line (d_exp ())) [c];
    
      let seen = (find_int_in_list !pastLoops (!(Cil.currentLoc).line)) in
      if seen then
  	  DF.GUnreachable
      else (
          pastLoops :=  (!(Cil.currentLoc).line)::!pastLoops;
    match c with
      | BinOp(op, lhs, rhs, resultType) ->
	E.log "Binop guard\n"; 
        DF.GUse (process_guard_binop op lhs rhs ll)
      | UnOp(op, e, resultType) -> (
        match op with
          | LNot -> (
            match e with
              | BinOp(op, lhs, rhs, resultType) -> 
                 DF.GUse (process_guard_binop op lhs rhs ll)
              | _ -> raise (UnsupportedOperation ("GGGG")) )
          | _ -> raise (UnsupportedOperation ("FFFF")) )
      | _ -> raise (UnsupportedOperation (string_of_exp c) )
	) 
  let filterStmt stm = true
end

module OddEven = DF.ForwardsDataFlow(OddEvenDF)

let collectVars (fd : fundec) : varmap list =
  (fd.sformals @ fd.slocals)
  |> L.filter (fun vi -> isIntegralType vi.vtype)
  |> L.map (fun vi -> (vi.vid, (vi,  Top )))

let computeOddEven (fd : fundec) : unit =
  try
    Cfg.clearCFGinfo fd;
    ignore(Cfg.cfgFun fd);
    let first_stmt = L.hd fd.sbody.bstmts in
    let vml = collectVars fd in
    IH.clear OddEvenDF.stmtStartData;
    IH.add OddEvenDF.stmtStartData first_stmt.sid vml;
    OddEven.compute [first_stmt]
  with
  | Failure "hd" ->
    if !debug then E.log "Function with no statements: %s\n" fd.svar.vname
  | Not_found ->
    E.error "No data for first statement? %s" fd.svar.vname

let getOddEvens (sid : int) : varmap list option =
  try Some(IH.find OddEvenDF.stmtStartData sid)
  with Not_found -> None

let instrOddEvens (il : instr list) (vml : varmap list) : varmap list list =
  (E.log "From oddevens\n");
  let proc_one hil i =
    match hil with
    | [] -> (varmap_list_handle_inst i vml) :: hil
    | vml':: rst as l -> (varmap_list_handle_inst i vml') :: l
  in
  il
  |> L.fold_left proc_one [vml]
  |> L.tl
  |> L.rev

let string_of_label (l : label) : string =
  match l with
  | Label(name, location, test) -> name^" "^(string_of_bool test)
  | Case(_,_) -> "case"
  | Default(_) -> "default"

let rec string_of_label_list (ll : label list) : string =
    match ll with
    | [] -> ""
    | h::t -> ((string_of_label h)^" "^(string_of_label_list t))

class vmlVisitorClass = object(self)
  inherit nopCilVisitor

  val mutable sid = -1
  val mutable vml_dat_lst = []
  val mutable cur_vml_dat = None

  method vstmt stm =
    ( if ((L.length stm.labels) > 0) then
      begin
      let lab = (L.hd stm.labels) in 
        ( match lab with 
          | Label(name, loc, test) -> (if name = "CHECK" then targetLine := loc.line else ())
          | _ -> ()
        )
      end
    else () );
    sid <- stm.sid;
    match getOddEvens sid with
    | None ->
      cur_vml_dat <- None;
      DoChildren
    | Some vml -> begin
      match stm.skind with
      | Instr il ->
(*        cur_vml_dat <- None;
        vml_dat_lst <- instrOddEvens il vml;
*)
        DoChildren
      | If(cond, onTrue, onFalse,loc) ->
(*	cur_vml_dat <- None;
	vml_dat_lst <- (varmap_list_handle_stmt stm vml)::vml_dat_lst; *)
        DoChildren
      | _ ->
        cur_vml_dat <- None;
        DoChildren
    end

  method vinst i =
    try
      let data = L.hd vml_dat_lst in
      cur_vml_dat <- Some(data);
      vml_dat_lst <- L.tl vml_dat_lst;
      DoChildren
    with Failure "hd" -> DoChildren

  method get_cur_vml () =
    match cur_vml_dat with
    | None -> getOddEvens sid
    | Some vml -> Some vml

end

 
class varUseReporterClass = object(self)
  inherit vmlVisitorClass as super

  method vvrbl (vi : varinfo) =
    match self#get_cur_vml () with
    | None -> SkipChildren
    | Some vml -> begin
      if L.mem_assoc vi.vid vml then begin
      end;
      SkipChildren
    end

end

let evenOddAnalysis (fd : fundec) (loc : location) : unit =
  computeOddEven fd;
  let vis = ((new varUseReporterClass) :> nopCilVisitor) in
  ignore(visitCilFunction vis fd); 
  HT.iter (fun k v -> (if !targetLine = k then (print_string (""^(z3_string_of_varmap_list v)^"\n(check-sat)\n(get-model)\n")) else () )) lineTable

let tut18 (f : file) : unit =
  iterGlobals f (onlyFunctions evenOddAnalysis)
