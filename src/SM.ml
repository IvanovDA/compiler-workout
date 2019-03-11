open GT       
open Language
       
(* The type for the stack machine instructions *)
@type insn =
(* binary operator                 *) | BINOP of string
(* put a constant on the stack     *) | CONST of int                 
(* read to stack                   *) | READ
(* write from stack                *) | WRITE
(* load a variable to the stack    *) | LD    of string
(* store a variable from the stack *) | ST    of string
(* a label                         *) | LABEL of string
(* unconditional jump              *) | JMP   of string                                                                                                                
(* conditional jump                *) | CJMP  of string * string
(* begins procedure definition     *) | BEGIN of string list * string list
(* end procedure definition        *) | END
(* calls a procedure               *) | CALL  of string * int with show			(*name, expected argument amount*)
                                                   
(* The type for the stack machine program *)                                                               
type prg = insn list

(* The type for the stack machine configuration: control stack, stack and configuration from statement
   interpreter
 *)
type config = (prg * State.t) list * int list * Stmt.config

(* Stack machine interpreter

     val eval : env -> config -> prg -> config

   Takes an environment, a configuration and a program, and returns a configuration as a result. The
   environment is used to locate a label to jump to (via method env#labeled <label_name>)
*)                         

let rec eval env (conf:config) p =
  let cst, stack, (s, i, o) = conf in
  match p with
    | [] -> conf
    | instr::p -> match instr with
      | BINOP op -> (
        match stack with
          | b::a::stack -> eval env (cst, [Language.Expr.evalBinop op a b] @ stack, (s, i, o)) p
          | a -> failwith (Printf.sprintf "[SM] Only one value on stack for binop %s" op)
          | [] -> failwith (Printf.sprintf "[SM] No values on stack for binop %s" op)
      )
      | CONST n -> eval env (cst, [n] @ stack, (s, i, o)) p
      | READ -> (
        match i with
          | n::i -> eval env (cst, [n] @ stack, (s, i, o)) p
          | _ -> failwith "[SM] No input data for READ instruction"
      )
      | WRITE -> (
        match stack with
          | n::stack -> eval env (cst, stack, (s, i, o @ [n])) p
          | _ -> failwith "[SM] Empty stack on WRITE instruction"
      )
      | LD v -> eval env (cst, [State.eval s v] @ stack, (s, i, o)) p
	  | ST v -> (
        match stack with
          | n::stack -> eval env (cst, stack, ((Language.State.update v n s), i, o)) p
          | _ -> failwith "[SM] Empty stack on ST instruction"
      )
      | LABEL _ -> eval env conf p
      | JMP label -> eval env conf (env#labeled label)
      | CJMP(needZero, label) -> (
        match stack with
          | [] -> failwith "[SM] CJMP without a value to evaluate"
          | n::stack ->
            if((n = 0) = (needZero = "z"))
              then eval env conf (env#labeled label)
              else eval env conf p
      )
	  | BEGIN(args, locs) ->
		let rec setArgs args stack s = match (args, stack) with
		  | ([], _) -> stack, s
		  | (arg::args, n::stack) ->
		    setArgs args stack (Language.State.update arg n s)
	      | _ -> failwith "[SM] Not enough arguments for a procedure call."
	    in
		let stack, s = setArgs args stack (State.push_scope s (args @ locs)) in
		eval env (cst, stack, (s, i, o)) p
	  | END -> (
	    match cst with
		  | [] -> conf
		  | (p, old_scope)::cst -> eval env (cst, stack, (State.drop_scope s old_scope, i, o)) p
	  )
	  | CALL(name, _) -> eval env ((p, s)::cst, stack, (s, i, o)) (env#labeled name)
      | _ -> failwith (Printf.sprintf "[SM] Unsupported instruction %s" (GT.transform(insn) new @insn[show] () instr))

(* Top-level evaluation

     val run : prg -> int list -> int list

   Takes a program, an input stream, and returns an output stream this program calculates
*)

let rec debugPrint p = match p with
  | i::p -> Printf.printf "%s\n" (GT.transform(insn) new @insn[show] () i); debugPrint p
  | _ -> ()

let run p i =
(*  debugPrint p; *)
  let module M = Map.Make (String) in
  let rec make_map m = function
  | []              -> m
  | (LABEL l) :: tl -> make_map (M.add l tl m) tl
  | _ :: tl         -> make_map m tl
  in
  let m = make_map M.empty p in
  let (_, _, (_, _, o)) = eval (object method labeled l = M.find l m end) ([], [], (State.empty, i, [])) p in o

(* Storage/generator for labels
     Stores last label indices for if, while, repeat, in that order
*)

type labelStorage = int * int * int

let labelName op counter = Printf.sprintf "LABEL_%s%d" op counter

let rec compileExpr t = 
  match t with
  | Language.Expr.Const n         -> [CONST n]
  | Language.Expr.Var v           -> [LD v]
  | Language.Expr.Binop(op, a, b) -> compileExpr a @ compileExpr b @ [BINOP op]

let rec compileImpl ((labelIf, labelWhile, labelRepeat) as labels) p = match p with
  | Language.Stmt.Read v             -> labels, [READ; ST v]
  | Language.Stmt.Write x            -> labels, compileExpr x @ [WRITE]
  | Language.Stmt.Assign(v, x)       -> labels, compileExpr x @ [ST v]
  | Language.Stmt.Seq(p1, p2)        -> 
    let labels, code1 = compileImpl labels p1 in
    let labels, code2 = compileImpl labels p2 in
    labels, code1 @ code2
  | Language.Stmt.Skip               -> labels, []
  | Language.Stmt.If(cond, p1, p2)   ->
    let thenLabel, exitLabel = labelName "IF" labelIf, labelName "IF" (labelIf + 1) in
    let labels, codeElse = compileImpl (labelIf + 2, labelWhile, labelRepeat) p2 in
    let labels, codeThen = compileImpl labels p1 in
    labels,
    compileExpr cond @ [CJMP("nz", thenLabel)] @
    codeElse @ [JMP(exitLabel); LABEL(thenLabel)] @ 
    codeThen @ [LABEL(exitLabel)]
  | Language.Stmt.While(cond, body)  ->
    let condLabel, bodyLabel = labelName "WHILE" labelWhile, labelName "WHILE" (labelWhile + 1) in
    let labels, codeBody = compileImpl (labelIf, labelWhile + 2, labelRepeat) body in
    labels,
    [JMP(condLabel); LABEL(bodyLabel)] @
    codeBody @ [LABEL(condLabel)] @
    compileExpr cond @ [CJMP("nz", bodyLabel)]
  | Language.Stmt.Repeat(body, cond) ->
    let bodyLabel = labelName "REPEAT" labelRepeat in
    let labels, codeBody = compileImpl (labelIf, labelWhile, labelRepeat + 1) body in
    labels,
    [LABEL(bodyLabel)] @ codeBody @ compileExpr cond @ [CJMP("z", bodyLabel)]
  | Language.Stmt.Call(name, argvals) ->
	let rec compileArgs args = match args with
	  | [] -> []
	  | (arg::args) -> compileExpr arg @ compileArgs args
	in
	let n = List.length argvals in
	labels, compileArgs argvals @ [CALL(name, n)]
  
let rec compileFuns labels funs = match funs with
  | [] -> labels, []
  | f::funs ->
    let (name, (args, locs, body)) = f in
	let labels, code = compileImpl labels body in
	let labels, rest = compileFuns labels funs in
	labels, [LABEL name; BEGIN(args, locs)] @ code @ [END] @ rest
  
(* Stack machine compiler

     val compile : Language.t -> prg

   Takes a program in the source language and returns an equivalent program for the
   stack machine
*)
  
let compile (funs, p) =
  let labels, funscode = compileFuns (0, 0, 0) funs in
  let _, code = compileImpl labels p in
  code @ [END] @ funscode
