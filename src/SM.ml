open GT       
open Language
       
(* The type for the stack machine instructions *)
@type insn =
(* binary operator                 *) | BINOP  of string
(* put a constant on the stack     *) | CONST  of int
(* load a variable to the stack    *) | LD     of string
(* store a variable from the stack *) | ST     of string
(* store in an array               *) | STA    of string * int
(* array name and indices amount   *)
(* store a string on the stack     *) | STRING of string
(* a label                         *) | LABEL  of string
(* unconditional jump              *) | JMP    of string                                                                                                                
(* conditional jump                *) | CJMP   of string * string
(* begins procedure definition     *) | BEGIN  of string * string list * string list
(* end procedure definition        *) | END
(* calls a procedure               *) | CALL   of string * int * bool
(* name, argc, is a function       *)
(* returns from a function         *) | RET    of bool
(* create an s-expression          *) | SEXP   of string * int
(* tag, length                     *)
(* checks the tag of S-expression  *) | TAG     of string
(* enters a scope                  *) | ENTER  of string list
(* leaves a scope                  *) | LEAVE
(* duplicates the top element      *) | DUP
(* swaps two top elements          *) | SWAP
(* drops the top element off       *) | DROP with show
                                                   
(* The type for the stack machine program *)                                                               
type prg = insn list
                            
(* The type for the stack machine configuration: control stack, stack and configuration from statement
   interpreter
 *)
type config = (prg * State.t) list * Value.t list * Expr.config

(* Stack machine interpreter

     val eval : env -> config -> prg -> config

   Takes an environment, a configuration and a program, and returns a configuration as a result. The
   environment is used to locate a label to jump to (via method env#labeled <label_name>)
*)                         

let split n l =
  let rec unzip (taken, rest) = function
  | 0 -> (List.rev taken, rest)
  | n -> match rest with
    | h::tl -> unzip (h::taken, tl) (n-1)
	| _ -> assert false
  in
  unzip ([], l) n

let rec evalCall env (conf:config) p instr =
  let cst, stack, (s, i, o, r) = conf in
  match instr with
    | CALL(name, argc, needRetval) -> (
      if env#is_label name
        then eval env ((p, s)::cst, stack, (s, i, o, r)) (env#labeled name)
        else eval env (env#builtin conf name argc needRetval) p
      )
    | _ -> failwith "Not a function call."
    
and eval env (conf:config) p =
  let cst, stack, (s, i, o, r) = conf in
  match p with
    | [] -> conf
    | instr::p -> 
	  (*Printf.printf "%s\n%!" (GT.transform(insn) new @insn[show] () instr);*)
	  match instr with
      | BINOP op -> (
        match stack with
          | b::a::stack -> eval env (cst, [Expr.evalBinop op a b] @ stack, (s, i, o, r)) p
          | _ -> failwith (Printf.sprintf "[SM] Not enough values on stack for binop %s" op)
      )
      | CONST n -> eval env (cst, [Value.Int n] @ stack, (s, i, o, r)) p
      | LD v -> eval env (cst, [State.eval s v] @ stack, (s, i, o, r)) p
      | ST v -> (
        match stack with
          | n::stack -> eval env (cst, stack, ((State.update v n s), i, o, r)) p
          | _ -> failwith "[SM] Empty stack on ST instruction"
      )
      | STA (v, argc) -> (
        match stack with
          | n::stack ->
            let ids, stack = split argc stack in
            eval env (cst, stack, ((Stmt.update s v n ids), i, o, r)) p 
          | _ -> failwith "[SM] Empty stack on STA instruction"
      )
      | STRING str -> eval env (cst, Value.String (Bytes.of_string str) :: stack, (s, i, o, r)) p
      | LABEL _ -> eval env conf p
      | JMP label -> eval env conf (env#labeled label)
      | CJMP(needZero, label) -> (
        match stack with
          | [] -> failwith "[SM] CJMP without a value to evaluate"
          | n::stack ->
            if((Value.to_int n = 0) = (needZero = "z"))
              then eval env (cst, stack, (s, i, o, r)) (env#labeled label)
              else eval env (cst, stack, (s, i, o, r)) p
      )
      | BEGIN(name, args, locs) ->
        let rec setArgs args stack s = match (args, stack) with
          | ([], _) -> stack, s
          | (arg::args, n::stack) ->
            setArgs args stack (State.update arg n s)
          | _ -> failwith "[SM] Not enough arguments for a procedure call."
        in
        let stack, s = setArgs args stack (State.enter s (args @ locs)) in
        eval env (cst, stack, (s, i, o, r)) p
      | END | RET _ -> (
        match cst with
          | [] -> conf
          | (p, old_scope)::cst -> eval env (cst, stack, (State.leave s old_scope, i, o, r)) p
      )
      | CALL(_, _, _) -> evalCall env conf p instr
      | SEXP(tag, argc) ->
        let children, stack = split argc stack in
        eval env (cst, Value.Sexp(tag, children)::stack, (s, i, o, r)) p
      | TAG(req_tag) -> (match stack with
		| sexp::stack -> (match sexp with
	      | Value.Sexp(val_tag, _) -> eval env (cst, Value.Int(if val_tag = req_tag then 1 else 0)::stack, (s, i, o, r)) p
		  | _ -> failwith "[SM] TAG: non-S-expression value")
		| _ -> failwith "[SM] TAG: empty stack")
      | DUP -> (match stack with
	    | x::stack -> eval env (cst, x::x::stack, (s, i, o, r)) p
		| _ -> failwith "[SM] DUP: empty stack")
      | SWAP -> (match stack with
	    | x::y::stack -> eval env (cst, y::x::stack, (s, i, o, r)) p
		| _ -> failwith "[SM] SWAP: need at least two values")
      | DROP -> (match stack with
	    | x::stack -> eval env (cst, stack, (s, i, o, r)) p
		| _ -> failwith "[SM] DROP: empty stack")
      | ENTER vars ->
        let vals, stack = split (List.length vars) stack in
        let rec consumeVals s vars vals = match vars, vals with
          | [], [] -> s
          | var::vars, value::vals ->
            let s = State.update var value s in consumeVals s vars vals
		  | _ -> assert false
        in
        let s = consumeVals (State.push s State.default vars) vars vals in
        eval env (cst, stack, (s, i, o, r)) p
      | LEAVE -> eval env (cst, stack, (State.drop s, i, o, r)) p
      (*| _ -> failwith (Printf.sprintf "[SM] Unsupported instruction: %s" (GT.transform(insn) new @insn[show] () instr))*)

(* Top-level evaluation

     val run : prg -> int list -> int list

   Takes a program, an input stream, and returns an output stream this program calculates
*)
  
let run p i =
  let module M = Map.Make (String) in
  let rec make_map m = function
  | []              -> m
  | (LABEL l) :: tl -> make_map (M.add l tl m) tl
  | _ :: tl         -> make_map m tl
  in
  let m = make_map M.empty p in
  let (_, _, (_, _, o, _)) = eval
    (object
       method is_label l = M.mem l m
       method labeled l = M.find l m
       method builtin (conf:config) f n p =
         let (cstack, stack, (st, i, o, r)) = conf in
         let args, stack' = split n stack in
         let (st, i, o, r) = Builtin.eval (st, i, o, Value.Void) args f in
         let stack'' = match p with
           | false -> stack'
           | true -> r::stack'
         in
         (cstack, stack'', (st, i, o, r))
     end)
    ([], [], (State.empty, i, [], Value.Void))
    p
  in o
  
(* Storage/generator for labels *)
module Labels = 
  struct
    type t = (string -> int)
  
    let default = fun tag -> 0
  
    let grab storage tag =
      let n = storage tag in
      let label = Printf.sprintf "%s_%d" tag n in
      (fun x -> if x = tag then n + 1 else storage x), label
    
    let grab2 storage tag =
      let storage, label_1 = grab storage tag in
      let storage, label_2 = grab storage tag in
      storage, label_1, label_2
  end

let rec compileCall name argvals ret =
  let n = List.length argvals in 
  compileArgs argvals @ [CALL(name, n, ret)]

and compileExpr t = 
  match t with
  | Expr.Const n             -> (
    match n with
      | Value.Int n          -> [CONST n]
      | Value.String str     -> [STRING (Bytes.to_string str)]
	  | _                    -> failwith "[SM] Non-int, non-string values are not compiled through Expr.Const (which is, frankly, a bit of a mistake)"
	  (* TODO get all the constant values to be handled through compileExpr, if possible.*)
  )
  | Expr.Var v               -> [LD v]
  | Expr.Binop(op, a, b)     -> compileExpr a @ compileExpr b @ [BINOP op]
  | Expr.Call(name, args)    -> compileArgs args @ [CALL(name, List.length args, true)]
  | Expr.Sexp(tag, children) -> compileArgs children @ [SEXP(tag, List.length children)]
  
and compileArgs args =
  let rec impl args = match args with
  | [] -> []
  | (arg::args) -> compileExpr arg @ impl args
  in impl (List.rev args)

and compileAccessList ids =
  let rec inner ids = 
    match ids with
     | [] -> []
     | id::ids -> [CONST id; CALL("BsexpElem", 2, true)] @ (compileAccessList ids)
  in
  inner (List.rev ids)
  
and compileCase labels cases =
  let rec checkList ps ids next = 
    let rec checkNext ps ids n next =
      match ps with
        | [] -> []
        | p::ps -> check p (n::ids) next @ checkNext ps ids (n + 1) next
    in
    checkNext ps ids 0 next
  (*maybe it makes sense to compare lengths first. nearly always we are more likely to not match a pattern than to match.*)
  and check pattern ids next = match pattern with
    | Stmt.Pattern.Wildcard | Stmt.Pattern.Ident _ -> []
    | Stmt.Pattern.Sexp (tag, children) -> [DUP] @ compileAccessList ids @ [TAG tag; CJMP("z", next)] @ checkList children ids next
  in
  let rec captures pattern = match pattern with
    | Stmt.Pattern.Wildcard -> []
    | Stmt.Pattern.Ident v -> [v]
    | Stmt.Pattern.Sexp (tag, children) -> List.concat(List.map captures children)
  in
  let bind pattern ids next = match pattern with
    | Stmt.Pattern.Wildcard -> []
    | Stmt.Pattern.Ident v -> compileAccessList ids
    | Stmt.Pattern.Sexp (tag, children) -> 
      let rec bindList ps ids next =      
        let rec bindNext ps ids n next =
          match ps with
            | [] -> []
            | p::ps -> 
              match p with
              | Stmt.Pattern.Wildcard -> []
              | Stmt.Pattern.Ident _ -> DUP :: compileAccessList (n::ids) @ [SWAP] @ bindNext ps ids (n + 1) next
              | Stmt.Pattern.Sexp (tag, children) -> bindList children (n::ids) next @ bindNext ps ids (n + 1) next
        in
        bindNext ps ids 0 next
      in
      bindList children ids next
  in
  let labels, endLabel = Labels.grab labels "CASE_END" in
  let compileOneCase labels case next = match case with (cause, effect) ->
    let labels, effect = compileImpl labels effect in
    labels, check cause [] next @ bind cause [] next @ [DROP; ENTER(List.rev(captures cause))] @ effect
  in
  let rec compileCases labels cases = match cases with
    | [] -> labels, [LABEL endLabel] (*shouldn't be possible, but just in case; better forbid on language level?*)
    | [case] -> 
      let labels, code = compileOneCase labels case endLabel in
      labels, code @ [LABEL endLabel]
    | case::cases ->
      let labels, nextLabel = Labels.grab labels "CASE" in
      let labels, code = compileOneCase labels case nextLabel in
      let labels, tail = compileCases labels cases in
      labels, code @ [JMP endLabel; LABEL nextLabel] @ tail
  in
  compileCases labels cases
    
and compileImpl (labels:Labels.t) p = match p with
  | Stmt.Assign(v, [], x)   -> labels, compileExpr x @ [ST v]
  | Stmt.Assign(v, is, x)   -> labels, compileArgs is @ compileExpr x @ [STA (v, List.length is)]
  | Stmt.Seq(p1, p2)        -> 
    let labels, code1 = compileImpl labels p1 in
    let labels, code2 = compileImpl labels p2 in
    labels, code1 @ code2
  | Stmt.Skip               -> labels, []
  | Stmt.If(cond, p1, p2)   ->
    let labels, thenLabel, exitLabel = Labels.grab2 labels "IF" in
    let labels, codeElse = compileImpl labels p2 in
    let labels, codeThen = compileImpl labels p1 in
    labels,
    compileExpr cond @ [CJMP("nz", thenLabel)] @
    codeElse @ [JMP(exitLabel); LABEL(thenLabel)] @ 
    codeThen @ [LABEL(exitLabel)]
  | Stmt.While(cond, body)  ->
    let labels, condLabel, bodyLabel = Labels.grab2 labels "WHILE" in
    let labels, codeBody = compileImpl labels body in
    labels,
    [JMP(condLabel); LABEL(bodyLabel)] @
    codeBody @ [LABEL(condLabel)] @
    compileExpr cond @ [CJMP("nz", bodyLabel)]
  | Stmt.Repeat(body, cond) ->
    let labels, bodyLabel = Labels.grab labels "REPEAT" in
    let labels, codeBody = compileImpl labels body in
    labels,
    [LABEL(bodyLabel)] @ codeBody @ compileExpr cond @ [CJMP("z", bodyLabel)]
  | Stmt.Call(name, argvals) -> labels, compileCall name argvals false
  | Stmt.Return(None)        -> labels, [RET false]
  | Stmt.Return(Some e)      -> labels, compileExpr e @ [RET true]
  | Stmt.Case(value, cases)  ->
    let labels, code = compileCase labels cases in
    labels, compileExpr value @ code
  | Stmt.Leave               -> labels, [LEAVE]
  
let rec compileFuns labels funs = match funs with
  | [] -> labels, []
  | f::funs ->
    let (name, (args, locs, body)) = f in
    let labels, code = compileImpl labels body in
    let labels, rest = compileFuns labels funs in
    labels, [LABEL name; BEGIN(name, args, locs)] @ code @ [END] @ rest
  
(* Stack machine compiler

     val compile : Language.t -> prg

   Takes a program in the source language and returns an equivalent program for the
   stack machine
*)

(*
let codelogf = open_out (Printf.sprintf "sm_code.log")

let rec debugPrint p = match p with
  | i::p -> Printf.fprintf codelogf "%s\n" (GT.transform(insn) new @insn[show] () i); debugPrint p
  | _ -> ()
*)
let compile (funs, p) =
  let labels, funscode = compileFuns Labels.default funs in
  let _, code = compileImpl labels p in
  let code = code @ [END] @ funscode in
  (*debugPrint code;*) code