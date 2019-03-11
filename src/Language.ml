(* Opening a library for generic programming (https://github.com/dboulytchev/GT).
   The library provides "@type ..." syntax extension and plugins like show, etc.
*)
open GT

(* Opening a library for combinator-based syntax analysis *)
open Ostap.Combinators
open Ostap

(* States *)
module State =
  struct
                                                                
    (* State: global state, local state, scope variables *)
    type t = {g : string -> int; l : string -> int; scope : string list}

    (* Empty state *)
    let empty =
      let e x = failwith (Printf.sprintf "Undefined variable: %s" x) in
      {g = e; l = e; scope = []}

    (* Update: non-destructively "modifies" the state s by binding the variable x 
       to value v and returns the new state w.r.t. a scope
    *)
    let update x v s =
      let u x v s = fun y -> if x = y then v else s y in
      if List.mem x s.scope then {s with l = u x v s.l} else {s with g = u x v s.g}

    (* Evals a variable in a state w.r.t. a scope *)
    let eval s x = (if List.mem x s.scope then s.l else s.g) x

    (* Creates a new scope, based on a given state *)
    let push_scope st xs = {empty with g = st.g; scope = xs}

    (* Drops a scope *)
    let drop_scope st st' = {st' with g = st.g}

  end

(* Simple expressions: syntax and semantics *)
module Expr =
  struct
    
    (* The type for expressions. Note, in regular OCaml there is no "@type..." 
       notation, it came from GT. 
    *)
    @type t =
    (* integer constant *) | Const of int
    (* variable         *) | Var   of string
    (* binary operator  *) | Binop of string * t * t with show

    (* Available binary operators:
        !!                   --- disjunction
        &&                   --- conjunction
        ==, !=, <=, <, >=, > --- comparisons
        +, -                 --- addition, subtraction
        *, /, %              --- multiplication, division, reminder
    *)

    let boolToInt n = if n then 1 else 0

    let to_func op =
      let bti   = function true -> 1 | _ -> 0 in
      let itb b = b <> 0 in
      let (|>) f g   = fun x y -> f (g x y) in
      match op with
      | "+"  -> (+)
      | "-"  -> (-)
      | "*"  -> ( * )
      | "/"  -> (/)
      | "%"  -> (mod)
      | "<"  -> bti |> (< )
      | "<=" -> bti |> (<=)
      | ">"  -> bti |> (> )
      | ">=" -> bti |> (>=)
      | "==" -> bti |> (= )
      | "!=" -> bti |> (<>)
      | "&&" -> fun x y -> bti (itb x && itb y)
      | "!!" -> fun x y -> bti (itb x || itb y)
      | _    -> failwith (Printf.sprintf "Unknown binary operator %s" op)    

    let evalBinop op a b = to_func op a b
	  
	(* Expression evaluator
         val eval : state -> expr -> int
     
       Takes a state and an expression, and returns the value of the expression in 
       the given state.
    *)
    let rec eval (st:State.t) (expr:t) =      
      match expr with
      | Const n -> n
      | Var   x -> State.eval st x
      | Binop (op, x, y) -> to_func op (eval st x) (eval st y)

    (* Expression parser. You can use the following terminals:

         IDENT   --- a non-empty identifier a-zA-Z[a-zA-Z0-9_]* as a string
         DECIMAL --- a decimal constant [0-9]+ as a string
                                                                                                                  
    *)
    ostap (                                      
      parse:
	  !(Ostap.Util.expr 
        (fun x -> x)
	    (Array.map (
		  fun (a, s) -> a, 
            List.map  (fun s -> ostap(- $(s)), (fun x y -> Binop (s, x, y))) s
          ) 
          [|                
			`Lefta, ["!!"];
			`Lefta, ["&&"];
			`Nona , ["=="; "!="; "<="; "<"; ">="; ">"];
			`Lefta, ["+" ; "-"];
			`Lefta, ["*" ; "/"; "%"];
          |] 
	    )
	    primary);
      
      primary:
        n:DECIMAL {Const n}
      | x:IDENT   {Var x}
      | -"(" parse -")"
    )
  end
                    
(* Simple statements: syntax and sematics *)
module Stmt =
  struct

    (* The type for statements *)
    @type t =
    (* read into the variable           *) | Read   of string
    (* write the value of an expression *) | Write  of Expr.t
    (* assignment                       *) | Assign of string * Expr.t
    (* composition                      *) | Seq    of t * t 
    (* empty statement                  *) | Skip
    (* conditional                      *) | If     of Expr.t * t * t
    (* loop with a pre-condition        *) | While  of Expr.t * t
    (* loop with a post-condition       *) | Repeat of t * Expr.t
    (* call a procedure                 *) | Call   of string * Expr.t list with show

    (* The type of configuration: a state, an input stream, an output stream *)
    type config = State.t * int list * int list 

    (* Statement evaluator

         val eval : env -> config -> t -> config

       Takes an environment, a configuration and a statement, and returns another configuration. The 
       environment supplies the following method

           method definition : string -> (string list, string list, t)

       which returns a list of formal parameters and a body for given definition
    *)

    let rec eval env ((s, i, o) as conf) (stmt:t) =
	  let checkCallCorrectness name args_expected args_given =
	    let exp_len = List.length args_expected in
		let act_len = List.length args_given in
		if exp_len != act_len
		  then failwith (Printf.sprintf "[Stmt] Incorrect amount of arguments in %s procedure call: needed %d, got %d" name exp_len act_len)
	  in
      (* Careful when functions will kick in: configuration can be mutated during expression evaluation *)
      match stmt with
        | Read v ->
          (
            match i with
              | n::i -> (State.update v n s), i, o
              | _ -> failwith "[Stmt] No input for Read statement"
          )
        | Write x            -> s, i, o @ [Expr.eval s x]
        | Assign(v, x)       -> (State.update v (Expr.eval s x) s), i, o
        | Seq(t1, t2)        -> eval env (eval env conf t1) t2
        | Skip               -> conf
        | If(cond, p1, p2)   -> if (Expr.eval s cond != 0) then eval env conf p1 else eval env conf p2
        | While(cond, body)  -> eval env conf (if (Expr.eval s cond != 0) then Seq(body, While(cond, body)) else Skip)
        | Repeat(body, cond) ->
          let (s, _, _) as conf = eval env conf body in
          eval env conf (if (Expr.eval s cond == 0) then Repeat(body, cond) else Skip)
        | Call (name, args_provided)  ->
		  let s_old = s in
	      let (args, locs, body) = env#definition name in
		  checkCallCorrectness name args args_provided;
	      let argvals = List.map (fun arg -> Expr.eval s arg) args_provided in
		  let rec setArgs vars vals s = match (vars, vals) with
		    | ([], []) -> s
			| (v::vars, n::vals) -> setArgs vars vals (State.update v n s)
		    | _ -> failwith "" (*Impossible, but Ocaml doesn't see that*)
	      in
		  let s = setArgs args argvals (State.push_scope s (args @ locs)) in
		  let (s, i, o) = eval env (s, i, o) body in
		  (State.drop_scope s s_old, i, o)
      
    (* Statement parser *)

    ostap (
	  else_branch:
          "fi" {Skip}
        | "else" body:!(parse) "fi" {body}
        | "elif" cond:!(Expr.parse) "then" s1:!(parse) s2:!(else_branch) {If(cond, s1, s2)};
      arglist:
	      v:!(Expr.parse) "," rest:!(arglist) {[v] @ rest} 
		| v:!(Expr.parse) {[v]}
		| empty {[]};
      stmt:
          v:IDENT ":=" e:!(Expr.parse) {Assign(v, e)}
		| name:IDENT "(" arglist:!(arglist) ")" {Call(name, arglist)}
        | "read" "(" x:IDENT ")" {Read x}
        | "write" "(" e:!(Expr.parse) ")" {Write e}
        | "if" cond:!(Expr.parse) "then" s1:!(parse) s2:!(else_branch) {If(cond, s1, s2)}
        | "while" cond:!(Expr.parse) "do" body:!(parse) "od" {While(cond, body)}
        | "for" init:!(stmt) "," cond:!(Expr.parse) "," step:!(stmt) "do" body:!(parse) "od" {Seq(init, While(cond, Seq(body, step)))}
        | "repeat" body:!(parse) "until" cond:!(Expr.parse) {Repeat(body, cond)}
        | "skip" {Skip};
            
      parse: s:stmt ";" rest:parse {Seq(s, rest)} | stmt
    )
  end

(* Function and procedure definitions *)
module Definition =
  struct

    (* The type for a definition: name, argument list, local variables, body *)
    type t = string * (string list * string list * Stmt.t)

    ostap (             
	  varlist:
	      v:IDENT "," rest:!(varlist) {[v] @ rest} 
		| v:IDENT {[v]}
		| empty {[]};
	  locals:
	      "local" varlist:!(varlist) {varlist}
		| empty {[]};
	  parse: "fun" name:IDENT "(" args:!(varlist) ")" locs:!(locals) "{" body:!(Stmt.parse) "}"{(name, (args, locs, body))}
    )

  end
    
(* The top-level definitions *)

(* The top-level syntax category is a pair of definition list and statement (program body) *)
type t = Definition.t list * Stmt.t    

(* Top-level evaluator

     eval : t -> int list -> int list

   Takes a program and its input stream, and returns the output stream
*)
let eval (defs, body) i =
  let module M = Map.Make (String) in
  let m        = List.fold_left (fun m ((name, _) as def) -> M.add name def m) M.empty defs in  
  let _, _, o  = Stmt.eval (object method definition f = snd @@ M.find f m end) (State.empty, i, []) body in o

(* Top-level parser *)
let parse = ostap (!(Definition.parse)* !(Stmt.parse))
