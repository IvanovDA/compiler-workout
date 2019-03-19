(* Opening a library for generic programming (https://github.com/dboulytchev/GT).
   The library provides "@type ..." syntax extension and plugins like show, etc.
*)
open GT

(* Opening a library for combinator-based syntax analysis *)
open Ostap
open Combinators

(* Integral types *)
module Value =
  struct
    @type t =
      | Int of int
      | String of bytes
      | Array of t array
      | Sexp of string * t list
      | Closure of string * t list
(* Function name, captured values; might be useful to add arity *)
(* Let's assume captured values are in the order they are mentioned in the func, for now - we need a natural order of some kind *)
      | Void
      
    let to_int = function
      | Int n -> n
      | _ -> failwith "Int value expected"
      
    let to_string = function 
      | String s -> Bytes.to_string s 
      | _ -> failwith "String value expected"

    let to_array = function
      | Array a -> a
      | _       -> failwith "Array value expected"
      
    let of_int    n = Int    n
    let of_string s = String s
    let of_array  a = Array  a
      
    let update_string s i x = Bytes.set s i x; s 
    let update_array  a i x = a.(i) <- x; a
  end
            
(* States *)
module State =
  struct
                                                                
    type t =
      | G of (string -> Value.t)
      | L of string list * (string -> Value.t) * t
      (* scope vars, local vars, enclosing state *)
    
    let default x = failwith (Printf.sprintf "Undefined variable: %s" x)
    
    (* Empty state *)
    let empty = G(default)
      
    (* Bind a variable to a value in a state *)
    let bind x v s = fun y -> if x = y then v else s y 

    (* Update: non-destructively "modifies" the state s by binding the variable x 
       to value v and returns the new state w.r.t. a scope
    *)
    let update x v s =
      match v with
      | Value.Void -> failwith "Assignment to void!"
      | _ ->
        let rec inner = function
        | G s -> G (bind x v s)
        | L (scope, s, enclosing) ->
           if List.mem x scope then L (scope, bind x v s, enclosing) else L (scope, s, inner enclosing)
        in
        inner s
      
    (* Evals a variable in a state w.r.t. a scope *)
    let rec eval s x =
      match s with
      | G s -> s x
      | L (scope, s, enclosing) -> if List.mem x scope then s x else eval enclosing x

    (* Creates a new scope, based on a given state *)
    let rec enter st xs =
      match st with
      | G _         -> L (xs, default, st)
      | L (_, _, e) -> enter e xs

    (* Drops a scope *)
    let leave st st' =
      let rec get = function
      | G _ as st -> st
      | L (_, _, e) -> get e
      in
      let g = get st in
      let rec recurse = function
      | L (scope, s, e) -> L (scope, s, recurse e)
      | G _             -> g
      in
      recurse st'
      
    (* Push a new local scope *)
    let push st s xs = L (xs, s, st)

    (* Drop a local scope *)
    let drop s = match s with
      | L (_, _, e) -> e
      | _ -> failwith "Can't drop the global scope"
    
  end
  
(* Builtins *)
module Builtin =
  struct
    let rec eval (st, i, o, _) args name = match name with
      | "read"      -> (match i with z::i' -> (st, i', o, (Value.Int z)) | _ -> failwith "Unexpected end of input")
      | "write"     -> (match List.hd args with
	    | Value.Int n -> (st, i, o @ [n], Value.Void)
		| Value.String s ->
		  Printf.printf "%s\n" (Bytes.to_string s);
		  (st, i, o, Value.Void)
		| _ -> failwith "Can't write a non-int, non-string value"
		)
	  
      | "elem"      -> (
        match args with
          | [b; j] ->        
            (st, i, o, let i = Value.to_int j in (match b with
              | Value.String s -> Value.of_int @@ Char.code (Bytes.get s i)
              | Value.Array  a -> a.(i)
              | Value.Sexp (_, s) -> List.nth s i
              | _ -> failwith "elem() was called for a non-enumerable structure"))
          | _ -> failwith "elem() needs two arguments")
      | "sexpElem"  -> eval (st, i, o, Value.Void) (List.rev args) "elem"
      | "length"    -> (st, i, o, Value.of_int (match List.hd args with
        | Value.Array a -> Array.length a
        | Value.String s -> Bytes.length s
        | Value.Sexp (_, s) -> List.length s
        | _ -> failwith "length() was called for a non-enumerable structure"))
	  | "arrayOfLen" -> (st, i, o, match args with [n] -> Value.of_array @@ Array.make (Value.to_int n) (Value.Void))
      | "array"     -> (st, i, o, match args with
	    | _::args -> Value.of_array @@ Array.of_list args
        | _ -> failwith "array() needs at least one value provided (array length)")
      | "isArray"   -> (match args with
        | [a] -> (st, i, o, Value.of_int @@ match a with Value.Array  _ -> 1 | _ -> 0)
        | _ -> failwith "isArray() needs a single argument provided")
      | "isString"  -> (match args with
        | [a] -> (st, i, o, Value.of_int @@ match a with Value.String _ -> 1 | _ -> 0)
        | _ -> failwith "isString() needs a single argument provided")
      | "stringval" -> let rec to_string = function
                          | Value.Int i       -> string_of_int i
                          | Value.String s    -> "\"" ^ Bytes.to_string s ^ "\""
                          | Value.Array a     -> "[" ^ String.concat ", " (List.map to_string (Array.to_list a)) ^ "]"
                          | Value.Sexp (m, a) -> "`" ^ m ^ if List.length a = 0 then "" else " (" ^ String.concat ", " (List.map to_string a) ^ ")"
                          | _                 -> failwith "A variable couldn't be cast to string."
                        in (st, i, o, (Value.of_string (Bytes.of_string (to_string (List.hd args)))))
      | _            -> failwith (Printf.sprintf "%s() is not a (built-in) function." name)
  end

(* Simple expressions: syntax and semantics *)
module Expr =
  struct
    
    (* The type for expressions. Note, in regular OCaml there is no "@type..." 
       notation, it came from GT. 
    *)
    @type t =
    (* constant         *) | Const       of Value.t
    (* variable         *) | Var         of string
    (* binary operator  *) | Binop       of string * t * t 
    (* S-expressions    *) | Sexp        of string * t list
    (* function call    *) | Call        of string * t list
    (* const or var func*)
    (* create a closure *) | Lambda      of string * string list
    (* need to define the callsite somehow - can as well be a string identifier for now *)
    (* probably something more reasonable later *)
    
    (* Available binary operators:
        !!                   --- disjunction
        &&                   --- conjunction
        ==, !=, <=, <, >=, > --- comparisons
        +, -                 --- addition, subtraction
        *, /, %              --- multiplication, division, reminder
    *)

    (* The type of configuration: a state, an input stream, an output stream, a return value *)
    type config = State.t * int list * int list * Value.t
                                                            
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

    let evalBinop op a b = match a, b with
      | Value.Int a, Value.Int b -> Value.Int (to_func op a b)
      | _ -> failwith "NIY: Binops on non-int values"
    
    (* Expression evaluator

          val eval : env -> config -> t -> config


       Takes an environment, a configuration and an expresion, and returns another configuration. The 
       environment supplies the following method

           method definition : env -> string -> int list -> config -> config

       which takes an environment (of the same type), a name of the function, a list of actual parameters and a configuration, 
       and returns the resulting configuration.
    *)
    
    let rec evalArgs env conf args = match args with
      | [] -> conf, []
      | arg::args -> (
        let (s, i, o, r) = eval env conf arg in
        match r with
          | Value.Void -> failwith "[Expr] An argument provided to a function is void." (* Sanity check *)
          | _ ->
            let conf, argvals = evalArgs env (s, i, o, r) args in
            conf, r::argvals
          )

    and eval env (conf:config) (expr:t) = 
      let (s, i, o, r) = conf in
      match expr with
      | Const n          -> (s, i, o, n)
      | Var   x          -> (s, i, o, (State.eval s x))
      | Binop(op, x, y)  ->
        let (s, i, o, r1) = eval env conf x in
        let (s, i, o, r2) = eval env (s, i, o, r1) y in
        (s, i, o, (evalBinop op r1 r2))
      | Sexp(x, args) ->
        let (s, i, o, _), args = evalArgs env conf args in
        (s, i, o, Value.Sexp(x, args))
      | Call(name, args) -> (
        try
          let closure = State.eval s name in
          match closure with
          | Value.Closure(name, captured) ->
            let (conf, argvals) = evalArgs env conf args in
            env#definition env name (captured @ argvals) conf
			(*env#definition env name argvals conf*)
          | _ -> failwith "Trying to call a non-function"
        with _ ->
          let (conf, argvals) = evalArgs env conf args in
          env#definition env name (argvals) conf)
      | Lambda(name, captured) ->
	    let (conf, captvals) = evalArgs env conf (List.map (fun x -> Var x) captured) in
	    (s, i, o, Value.Closure(name, captvals))
      
      (* If you :thonk: about it, a normal call is just a closure with no captured variables *)
      (* Except it isn't, because a closure generally doesn't interact with global variables *)
      (* Okay; let's say for now that we want to capture variables explicitly when creating a closure then *)
  end
                    
(* Simple statements: syntax and sematics *)
module Stmt =
  struct
  
    module Pattern = 
      struct
        @type t =
        | Sexp     of string * t list
        | Ident    of string
        | Wildcard
        with show
        
    end
    
    (* The type for statements *)
    @type t =
    (* assignment                       *) | Assign of string * Expr.t list * Expr.t
    (* composition                      *) | Seq    of t * t 
    (* empty statement                  *) | Skip
    (* conditional                      *) | If     of Expr.t * t * t
    (* loop with a pre-condition        *) | While  of Expr.t * t
    (* loop with a post-condition       *) | Repeat of t * Expr.t
    (* pattern-matching                 *) | Case   of Expr.t * (Pattern.t * t) list
    (* leave scope                      *) | Leave
    (* call a procedure                 *) | Call   of string * Expr.t list
    (* return statement                 *) | Return of Expr.t option
    
    (* The type of configuration: a state, an input stream, an output stream *)
    type config = State.t * int list * int list 

    (* Statement evaluator

         val eval : env -> config -> t -> t -> config

       Takes an environment, a configuration, a statement and a residual statement, and returns another configuration. The 
       environment supplies the following method

           method definition : string -> (string list, string list, t)

       which returns a list of formal parameters and a body for given definition
    *)

    let retValInt conf = let (_, _, _, r) = conf in Value.to_int r
    
    (* Maybe define it as a builtin instead, eh *)
    let update st x v is =
      let rec update a v = function
      | []    -> v           
      | i::tl ->
          let i = Value.to_int i in 
          (match a with
            | Value.String s when tl = [] -> Value.String (Value.update_string s i (Char.chr @@ Value.to_int v))
            | Value.Array a               -> Value.Array (Value.update_array  a i (update a.(i) v tl))
            | _                           -> failwith "STA operation impossible"
          ) 
      in
      State.update x (match is with | [] -> v | _ -> update (State.eval st x) v is) st

    let rec eval env (conf:Expr.config) k (stmt:t) =
      if (stmt = Skip) && (k = Skip)
        then conf
        else match stmt with
          | Skip -> eval env conf Skip k
          | Assign(v, args, x) ->
            let conf, argvals = Expr.evalArgs env conf args in
            let (s, i, o, r) = Expr.eval env conf x in
            let s = update s v r argvals in
            eval env (s, i, o, r) Skip k
          | Seq(t, Skip) | Seq(Skip, t) ->
            eval env conf k t
          | Seq(t1, t2) -> 
            eval env conf (Seq(t2, k)) t1
          | If(cond, p1, p2) -> 
            let conf = Expr.eval env conf cond in
            if ((retValInt conf) != 0) then eval env conf k p1 else eval env conf k p2
          | While(cond, body)  ->
            let conf = Expr.eval env conf cond in
            if ((retValInt conf) != 0)
              then eval env conf k (Seq(body, While(cond, body)))
              else eval env conf Skip k
          | Repeat(body, cond) ->
            let conf = eval env conf Skip body in
            let conf = Expr.eval env conf cond in
            eval env conf k (if ((retValInt conf) = 0) then Repeat(body, cond) else Skip)
          | Call(closure, argvals) ->
            let conf = Expr.eval env conf (Expr.Call(closure, argvals)) in
            eval env conf Skip k
          | Return(Some t) ->
            let conf = Expr.eval env conf t in conf
          | Return(None) -> conf
          | Leave -> 
            let (s, i, o, r) = conf in
            eval env (State.drop s, i, o, r) Skip k 
          | Case(e, cases) ->
            let (s, i, o, r) = Expr.eval env conf e in
            (* returns an optional list of variables and list of bound values *)
            let rec check case r =
              match case with
              | Pattern.Wildcard -> Some ([], [])
              | Pattern.Ident v -> Some ([v], [r])
              | Pattern.Sexp(tag_p, subs_p) -> (match r with
                | Value.Sexp(tag_v, subs_v) -> (
                  (* didn't know ocaml sees "<>" as structural integrity; that ate way too much time*)
                  if (tag_p <> tag_v) || (List.length subs_p != List.length subs_v) 
                    then None
                    else 
                      let rec inner (subs_p: Pattern.t list) subs_v =
                        match subs_p, subs_v with 
                          | ([], []) -> Some ([], [])
                          | (p::subs_p, v::subs_v) -> (
                            let attempt = check p v in
                            match attempt with
                              | None -> None
                              | Some (p, v) ->
                                let restattempt = inner subs_p subs_v in
                                match restattempt with
                                  | None -> None
                                  | Some (rest_p, rest_v) -> Some(p @ rest_p, v @ rest_v))
                          | _ -> assert false
                      in inner subs_p subs_v) 
                | _ -> failwith "Incorrect pattern - a non-pattern child")
            in let rec switch r cases = match cases with
              | [] -> None
              | (cause, effect)::cases ->
                let res = check cause r in
                match res with
                  | None -> switch r cases
                  | Some (p, v) -> Some (p, v, effect)
            in let branch = switch r cases in
            match branch with
              | None -> failwith "No pattern matches."
              | Some (vars, vals, effect) ->
                let s = State.push s State.default vars in
                let rec massUpdate xs vs s =
                  match xs, vs with
                    | ([], []) -> s
                    | ([x], [v]) -> State.update x v s
                    | (x::xs, v::vs) -> massUpdate xs vs (State.update x v s)
                    | _ -> assert false
                in
                let s = massUpdate vars vals s in
                eval env (s, i, o, Value.Void) Skip effect
          (*| _ -> failwith "[Stmt] Unsupported statement"*)
         
  end

(* Function and procedure definitions *)
module Definition =
  struct

    type impl = (string list * string list * string list * Stmt.t)
  
    (* The type for a definition: name, captured variables list, argument list, local variables, body *)
    type t = string * impl

    let makeDeclaration (name, (captured, args, locs, body)) =
      Stmt.Assign(name, [], Expr.Const(Value.Closure(name, [])))

  end

(* Sorry, this is very, very ugly *)
module LambdaLifter = 
  struct
    let storage : (Definition.t list) ref = ref []
  
    let counter = ref 0
    
    (* "A" because A-nonymous functions and "L" is taken *)
    let newName () =
      let id = !counter in
      counter := !counter + 1;
      Printf.sprintf "A%d" id

    let add_and_name impl =
	  let rec findDef impl defs = match defs with
	    | [] -> None
		| (name, d_impl)::defs ->
		  if (d_impl = impl)
		    then Some name
		  else
		    findDef impl defs
	  in
	  let name = findDef impl !storage in
	  match name with
	    | Some name -> name
		| None ->
		  let name = newName () in
          storage := (name, impl) :: !storage;
		  name
	
    let res () = !storage
      
  end
  
module Parser =
  struct
    let lvalueToRvalue (x, ids) =
      let rec inner x ids = 
        match ids with
          | [] -> x
          | id::ids -> inner (Expr.Call("elem", [x; id])) ids
      in inner (Var x) ids
    
    ostap (
      (* Expressions *)
      parse_expr:
      !(Ostap.Util.expr 
        (fun x -> x)
        (Array.map (
          fun (a, s) -> a, 
            List.map  (fun s -> ostap(- $(s)), (fun x y -> Expr.Binop (s, x, y))) s
          ) 
          [|                
            `Lefta, ["!!"];
            `Lefta, ["&&"];
            `Lefta, ["=="; "!="; "<="; "<"; ">="; ">"];
            `Lefta, ["+" ; "-"];
            `Lefta, ["*" ; "/"; "%"];
          |] 
        )
        stringified_if_necessary);
        
      (* TODO: allow postfix chaining *)
        
      stringified_if_necessary:
        v:!(expr_primary) ".string" {Expr.Call("stringval", [v])}
      | v:!(expr_primary) {v};

      exprlist:
        v:!(parse_expr) "," rest:!(exprlist) {[v] @ rest} 
      | v:!(parse_expr) {[v]}
      | empty {[]};
        
      acclist:
        "[" id:!(parse_expr) "]" rest:!(acclist) {[id] @ rest}
      | empty {[]};
        
      lvalue:
        x:IDENT ids:!(acclist) {(x, ids)};
      
	  (* Here's a problem: what are the non-arg, non-captured vars in body? *)
	  (* Are they local or global? They sure aren't local to call/definition site scope because that's nonsense *)
	  (* We have considered everything global by default before; so why not keep at it? *)
      lambda:
        "lambda" "[" captured:!(varlist) "]" varlist:!(varlist) ":" "{" body:!(parse_stmt) "}" {
          let name = LambdaLifter.add_and_name (captured, varlist, [], body) in
          Expr.Lambda(name, captured)
        }
	  | "lambda" varlist:!(varlist) ":" "{" body:!(parse_stmt) "}" {
          let name = LambdaLifter.add_and_name ([], varlist, [], body) in
          Expr.Lambda(name, [])
        };
      
      expr_primary:
        n:DECIMAL {Expr.Const (Value.Int n)}
      | c:CHAR {Expr.Const (Value.Int (Char.code c))}
      | s:STRING {Expr.Const (Value.String (Bytes.of_string (String.sub s 1 (String.length s - 2))))}
      | "[" exprlist:!(exprlist) "]" {Expr.Call("array", [Expr.Const (Value.Int (List.length exprlist))] @ exprlist)}
      | lambda:!(lambda) {lambda}
      | name:IDENT "(" arglist:!(exprlist) ")" {Expr.Call(name, arglist)}
      | "`" tag:IDENT "(" exprlist:!(exprlist) ")" {Expr.Sexp(tag, exprlist)}
      | "`" tag:IDENT {Expr.Sexp(tag, [])}
      | v:!(lvalue) ".length" {Expr.Call("length", [lvalueToRvalue v])}
      | x:!(lvalue) {lvalueToRvalue x}
      | -"(" parse_expr -")";
      
      (* Patterns *)
      identlist:
        x:!(parse_pattern) "," rest:!(identlist) {[x] @ rest}
      | x:IDENT "," rest:!(identlist) {[Stmt.Pattern.Ident x] @ rest}
      | x:!(parse_pattern) {[x]}
      | x:IDENT {[Stmt.Pattern.Ident x]}
      | empty {[]};

      parse_pattern:
        "_" {Stmt.Pattern.Wildcard}
      | "`" x:IDENT "(" idents:!(identlist) ")" {Stmt.Pattern.Sexp(x, idents)}
      | "`" x:IDENT {Stmt.Pattern.Sexp(x, [])};
      
      (* Statements *)
      else_branch:
        "fi" {Stmt.Skip}
      | "else" body:!(parse_stmt) "fi" {body}
      | "elif" cond:!(parse_expr) "then" s1:!(parse_stmt) s2:!(else_branch) {Stmt.If(cond, s1, s2)};
      
      case_body:
        cause:!(parse_pattern) "->" effect:!(parse_stmt) "|" rest:!(case_body) {[(cause, Stmt.Seq(effect, Stmt.Leave))] @ rest}
      | cause:!(parse_pattern) "->" effect:!(parse_stmt) {[(cause, Stmt.Seq(effect, Stmt.Leave))]};
      
      varlist:
        v:IDENT "," rest:!(varlist) {[v] @ rest} 
      | v:IDENT {[v]}
      | empty {[]};
      
      stmt:
        v:!(lvalue) ":=" e:!(parse_expr) {let (x, ids) = v in Stmt.Assign(x, ids, e)}
      | name:IDENT "(" arglist:!(exprlist) ")" {Stmt.Call(name, arglist)}
      | "if" cond:!(parse_expr) "then" s1:!(parse_stmt) s2:!(else_branch) {Stmt.If(cond, s1, s2)}
      | "while" cond:!(parse_expr) "do" body:!(parse_stmt) "od" {Stmt.While(cond, body)}
      | "for" init:!(parse_stmt) "," cond:!(parse_expr) "," step:!(parse_stmt) "do" body:!(parse_stmt) "od" {Stmt.Seq(init, Stmt.While(cond, Stmt.Seq(body, step)))}
      | "repeat" body:!(parse_stmt) "until" cond:!(parse_expr) {Stmt.Repeat(body, cond)}
      | "skip" {Stmt.Skip}
      | "return" retval:!(parse_expr) {Stmt.Return(Some retval)}
      | "return" {Stmt.Return(None)}
      | "case" x:!(parse_expr) "of" cases:!(case_body) "esac" {Stmt.Case(x, cases)};
      
      parse_stmt: s:stmt ";" rest:parse_stmt {Stmt.Seq(s, rest)} | stmt;
      
      (* Function definitions *)
      locals:
          "local" varlist:!(varlist) {varlist}
        | empty {[]};
        
      parse_func: "fun" name:IDENT "(" args:!(varlist) ")" locs:!(locals) "{" body:!(parse_stmt) "}"{((name), ([], args, locs, body))}
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
  let fundecls = List.map (fun x -> Definition.makeDeclaration x) defs in
  let body = List.fold_left (fun x y -> Stmt.Seq(y, x)) body fundecls in
  let _, _, o, _ =
    Stmt.eval
      (object
         method definition env f (args:Value.t list) (st, i, o, r) =
           try
             let cpt, xs, locs, s = snd @@ M.find f m in
             let st'              = List.fold_left (fun st (x, a) -> State.update x a st) (State.enter st (cpt @ xs @ locs)) (List.combine (cpt @ xs) args) in
             let st'', i', o', r' = Stmt.eval env (st', i, o, r) Stmt.Skip s in
             (State.leave st'' st, i', o', r')
           with Not_found -> Builtin.eval (st, i, o, r) args f
       end)
      (State.empty, i, [], Value.Void)
      Stmt.Skip
      body
  in
  o

(* Top-level parser *)
let parse = ostap (!(Parser.parse_func)* !(Parser.parse_stmt))
