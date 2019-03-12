open GT       
open Language
       
(* The type for the stack machine instructions *)
@type insn =
(* binary operator                 *) | BINOP of string
(* put a constant on the stack     *) | CONST of int                 
(* load a variable to the stack    *) | LD    of string
(* store a variable from the stack *) | ST    of string
(* a label                         *) | LABEL of string
(* unconditional jump              *) | JMP   of string                                                                                                                
(* conditional jump                *) | CJMP  of string * string
(* begins procedure definition     *) | BEGIN of string * string list * string list
(* end procedure definition        *) | END
(* calls a procedure               *) | CALL  of string * int * bool
(* name, argc, is a function       *)
(* returns from a function         *) | RET   of bool with show
                                                   
(* The type for the stack machine program *)                                                               
type prg = insn list
                            
(* The type for the stack machine configuration: control stack, stack and configuration from statement
   interpreter
 *)
type config = (prg * State.t) list * int list * Expr.config

(* Stack machine interpreter

     val eval : env -> config -> prg -> config

   Takes an environment, a configuration and a program, and returns a configuration as a result. The
   environment is used to locate a label to jump to (via method env#labeled <label_name>)
*)                         

let rec evalCall env (conf:config) p instr =
  let cst, stack, (s, i, o, r) = conf in
  match instr with
    | CALL(name, argc, _) -> (
	    try 
    	  eval env ((p, s)::cst, stack, (s, i, o, r)) (env#labeled name)
        with Not_found ->
		  let conf = env#builtin (cst, stack, (s, i, o, r)) name argc in
		  eval env conf p
	  )
	| _ -> failwith "Not a function call."
	
and eval env (conf:config) p =
  let cst, stack, (s, i, o, r) = conf in
  match p with
    | [] -> conf
    | instr::p -> match instr with
      | BINOP op -> (
        match stack with
          | b::a::stack -> eval env (cst, [Value.to_int (Expr.evalBinop op (Value.Int a) (Value.Int b))] @ stack, (s, i, o, r)) p
          | _ -> failwith (Printf.sprintf "[SM] Not enough values on stack for binop %s" op)
      )
      | CONST n -> eval env (cst, [n] @ stack, (s, i, o, r)) p
      | LD v -> eval env (cst, [Value.to_int (State.eval s v)] @ stack, (s, i, o, r)) p
      | ST v -> (
        match stack with
          | n::stack -> eval env (cst, stack, ((State.update v (Value.Int n) s), i, o, r)) p
          | _ -> failwith "[SM] Empty stack on ST instruction"
      )
      | LABEL _ -> eval env conf p
      | JMP label -> eval env conf (env#labeled label)
      | CJMP(needZero, label) -> (
        match stack with
          | [] -> failwith "[SM] CJMP without a value to evaluate"
          | n::stack ->
            if((n = 0) = (needZero = "z"))
              then eval env (cst, stack, (s, i, o, r)) (env#labeled label)
              else eval env (cst, stack, (s, i, o, r)) p
      )
      | BEGIN(name, args, locs) ->
        let rec setArgs args stack s = match (args, stack) with
          | ([], _) -> stack, s
          | (arg::args, n::stack) ->
            setArgs args stack (State.update arg (Value.Int n) s)
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
      | _ -> failwith (Printf.sprintf "[SM] Unsupported instruction %s" (GT.transform(insn) new @insn[show] () instr))

(* Top-level evaluation

     val run : prg -> int list -> int list

   Takes a program, an input stream, and returns an output stream this program calculates
*)

let split n l =
  let rec unzip (taken, rest) = function
  | 0 -> (List.rev taken, rest)
  | n -> let h::tl = rest in unzip (h::taken, tl) (n-1)
  in
  unzip ([], l) n
  
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
       method builtin (conf:config) f n =
	     let (cstack, stack, (st, i, o, r)) = conf in
         let f = match f.[0] with 'L' -> String.sub f 1 (String.length f - 1) | _ -> f in
         let args, stack' = split n stack in
         let (st, i, o, r) = Language.Builtin.eval (st, i, o, Language.Value.Void) (List.rev (List.map (fun x -> Language.Value.Int x) args)) f in
         let stack'' = match r with
		   | Language.Value.Void -> stack'
		   | Language.Value.Int n -> n::stack'
		 in
         (cstack, stack'', (st, i, o, r))
     end)
	([], [], (State.empty, i, [], Value.Void))
	p
  in o
  
(* Storage/generator for labels
     Stores last label indices for if, while, repeat, in that order
*)

type labelStorage = int * int * int

let labelName op counter = Printf.sprintf "LABEL_%s%d" op counter

let rec compileExpr t = 
  match t with
  | Language.Expr.Const (Value.Int n) -> [CONST n]
  | Language.Expr.Var v            -> [LD v]
  | Language.Expr.Binop(op, a, b)  -> compileExpr a @ compileExpr b @ [BINOP op]
  | Language.Expr.Call(name, args) -> compileArgs args @ [CALL(name, List.length args, true)]
  | _ -> failwith "Trying to compile a non-int value"

and compileArgs args =
  let rec impl args = match args with
  | [] -> []
  | (arg::args) -> compileExpr arg @ compileArgs args
  in impl (List.rev args)

and compileImpl ((labelIf, labelWhile, labelRepeat) as labels) p = match p with
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
    let n = List.length argvals in 
    labels, compileArgs argvals @ [CALL(name, n, false)]
  | Language.Stmt.Return(None)        -> labels, [RET false]
  | Language.Stmt.Return(Some e)      -> labels, compileExpr e @ [RET true]
  
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

let compile (funs, p) =
  let labels, funscode = compileFuns (0, 0, 0) funs in
  let _, code = compileImpl labels p in
  code @ [END] @ funscode
