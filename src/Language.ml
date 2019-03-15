(* Opening a library for generic programming (https://github.com/dboulytchev/GT).
   The library provides "@type ..." syntax extension and plugins like show, etc.
*)
open GT

(* Opening a library for combinator-based syntax analysis *)
open Ostap
open Combinators
          
module Value =
  struct
    @type t =
      | Int of int
      | String of bytes
      | Array of t array
      | Sexp of string * t list
      | Void
      
    let to_int = function
      | Int n -> n
      | String s -> failwith (Printf.sprintf "Wanted an int, got %s" (Bytes.to_string s))
      (*| _ -> failwith "Int value expected"*)
      
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
    let drop (L (_, _, e)) = e
    
  end
  
(* Builtins *)
module Builtin =
  struct
    let eval (st, i, o, _) args name = match name with
      | "Lread"     -> (match i with z::i' -> (st, i', o, (Value.Int z)) | _ -> failwith "Unexpected end of input")
      | "Lwrite"    -> (st, i, o @ [Value.to_int @@ List.hd args], Value.Void)
      | "Belem"     ->
        let [b; j] = args in
        (st, i, o, let i = Value.to_int j in
        (match b with
          | Value.String s -> Value.of_int @@ Char.code (Bytes.get s i)
          | Value.Array  a -> a.(i)
        ))         
      | "Blength"  -> (st, i, o, Value.of_int (match List.hd args with Value.Array a -> Array.length a | Value.String s -> Bytes.length s))
      | "Barray"   -> (st, i, o, match args with n::args -> Value.of_array @@ Array.of_list args)
      | "LisArray"  -> let [a] = args in (st, i, o, Value.of_int @@ match a with Value.Array  _ -> 1 | _ -> 0)
      | "LisString" -> let [a] = args in (st, i, o, Value.of_int @@ match a with Value.String _ -> 1 | _ -> 0)
      | _          -> failwith (Printf.sprintf "%s() is not a (built-in) function." name)
  end

(* Simple expressions: syntax and semantics *)
module Expr =
  struct
    
    (* The type for expressions. Note, in regular OCaml there is no "@type..." 
       notation, it came from GT. 
    *)
    @type t =
    (* constant         *) | Const  of Value.t
    (* variable         *) | Var    of string
    (* binary operator  *) | Binop  of string * t * t 
    (* S-expressions    *) | Sexp      of string * t list
    (* function call    *) | Call   of string * t list
    
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
      | Call(name, args) ->
        let (conf, argvals) = evalArgs env conf args in
        env#definition env name argvals conf
        
    (* Expression parser. You can use the following terminals:

         IDENT   --- a non-empty identifier a-zA-Z[a-zA-Z0-9_]* as a string
         DECIMAL --- a decimal constant [0-9]+ as a string
                                                                                                                  
    *)

    let lvalueToRvalue (x, ids) =
      let rec inner x ids = 
        match ids with
          | [] -> x
          | id::ids -> inner (Call("Belem", [x; id])) ids
      in inner (Var x) ids
      
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

      exprlist:
        v:!(parse) "," rest:!(exprlist) {[v] @ rest} 
      | v:!(parse) {[v]}
      | empty {[]};
        
      acclist:
        "[" id:!(primary) "]" rest:!(acclist) {[id] @ rest}
      | empty {[]};
        
      lvalue:
        x:IDENT ids:!(acclist) {(x, ids)};
      
      primary:
        n:DECIMAL {Const (Value.Int n)}
      | c:CHAR {Const (Value.Int (Char.code c))}
      | s:STRING {Const (Value.String (Bytes.of_string (String.sub s 1 (String.length s - 2))))}
      | "[" exprlist:!(exprlist) "]" {Call("Barray", [Const (Value.Int (List.length exprlist))] @ exprlist)}
      | name:IDENT "(" arglist:!(exprlist) ")" {Call("L" ^ name, arglist)}
      | "`" tag:IDENT "(" exprlist:!(exprlist) ")" {Sexp(tag, exprlist)}
      | "`" tag:IDENT {Sexp(tag, [])}
      | v:!(lvalue) ".length" {Call("Blength", [lvalueToRvalue v])}
      | x:!(lvalue) {lvalueToRvalue x}
      | -"(" parse -")"
    )
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
        
      ostap (
        identlist:
            x:!(parse) "," rest:!(identlist) {[x] @ rest}
          | x:IDENT "," rest:!(identlist) {[Ident x] @ rest}
          | x:!(parse) {[x]}
          | x:IDENT {[Ident x]}
          | empty {[]};
        
        parse:
            "_" {Wildcard}
          | "`" x:IDENT "(" idents:!(identlist) ")" {Sexp(x, idents)}
          | "`" x:IDENT {Sexp(x, [])}
      )
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
          ) 
      in
      State.update x (match is with | [] -> v | _ -> update (State.eval st x) v is) st

    let rec eval env (conf:Expr.config) k (stmt:t) =
      if (stmt = Skip)
        then (
          if (k = Skip)
            then conf
            else eval env conf Skip k
        )
        else
        match stmt with
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
          | Call(name, args_provided) ->
            let conf = Expr.eval env conf (Expr.Call(name, args_provided)) in
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
                Value.Sexp(tag_v, subs_v) -> (
                  (* didn't know ocaml sees "<>" as structural integrity; that ate way too much time*)
                  if (tag_p <> tag_v) or (List.length subs_p != List.length subs_v) 
                    then None
                    else 
                      let rec inner (subs_p: Pattern.t list) subs_v =
                        match subs_p, subs_v with 
                          | ([], []) -> Some ([], [])
                          | (p::subs_p, v::subs_v) ->
                            let attempt = check p v in
                            match attempt with
                              | None -> None
                              | Some (p, v) ->
                                let restattempt = inner subs_p subs_v in
                                match restattempt with
                                  | None -> None
                                  | Some (rest_p, rest_v) -> Some(p @ rest_p, v @ rest_v)
                      in inner subs_p subs_v
                  ) 
                )
            in let rec switch r cases = match cases with
              | [] -> None
              | (cause, effect)::cases ->
                let res = check cause r in
                match res with
                  | None -> switch r cases
                  | Some (p, v) -> Some (p, v, effect)
            in let branch = switch r cases in
            match branch with
              | None -> close_out outf; failwith "No pattern matches."
              | Some (vars, vals, effect) ->
                let s = State.push s State.default vars in
                let rec massUpdate xs vs s =
                  match xs, vs with
                    | ([], []) -> s
                    | ([x], [v]) -> State.update x v s
                    | (x::xs, v::vs) -> massUpdate xs vs (State.update x v s)
                in
                let s = massUpdate vars vals s in
                eval env (s, i, o, Value.Void) Skip effect
          (*| _ -> failwith "[Stmt] Unsupported statement"*)
         
    (* Statement parser *)
    ostap (
      else_branch:
          "fi" {Skip}
        | "else" body:!(parse) "fi" {body}
        | "elif" cond:!(Expr.parse) "then" s1:!(parse) s2:!(else_branch) {If(cond, s1, s2)};
      case_body:
          cause:!(Pattern.parse) "->" effect:!(parse) "|" rest:!(case_body) {[(cause, Seq(effect, Leave))] @ rest}
        | cause:!(Pattern.parse) "->" effect:!(parse) {[(cause, Seq(effect, Leave))]};
      stmt:
          v:!(Expr.lvalue) ":=" e:!(Expr.parse) {let (x, ids) = v in Assign(x, ids, e)}
        | name:IDENT "(" arglist:!(Expr.exprlist) ")" {Call("L" ^ name, arglist)}
        | "if" cond:!(Expr.parse) "then" s1:!(parse) s2:!(else_branch) {If(cond, s1, s2)}
        | "while" cond:!(Expr.parse) "do" body:!(parse) "od" {While(cond, body)}
        | "for" init:!(stmt) "," cond:!(Expr.parse) "," step:!(stmt) "do" body:!(parse) "od" {Seq(init, While(cond, Seq(body, step)))}
        | "repeat" body:!(parse) "until" cond:!(Expr.parse) {Repeat(body, cond)}
        | "skip" {Skip}
        | "return" retval:!(Expr.parse) {Return(Some retval)}
        | "return" {Return(None)}
        | "case" x:!(Expr.parse) "of" cases:!(case_body) "esac" {Case(x, cases)};
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
      parse: "fun" name:IDENT "(" args:!(varlist) ")" locs:!(locals) "{" body:!(Stmt.parse) "}"{(("L" ^ name), (args, locs, body))}
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
  let m          = List.fold_left (fun m ((name, _) as def) -> M.add name def m) M.empty defs in  
  let _, _, o, _ =
    Stmt.eval
      (object
         method definition env f (args:Value.t list) (st, i, o, r) =
           try
             let xs, locs, s      = snd @@ M.find f m in
             let st'              = List.fold_left (fun st (x, a) -> State.update x a st) (State.enter st (xs @ locs)) (List.combine xs args) in
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
let parse = ostap (!(Definition.parse)* !(Stmt.parse))
