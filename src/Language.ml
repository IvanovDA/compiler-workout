(* Opening a library for generic programming (https://github.com/dboulytchev/GT).
   The library provides "@type ..." syntax extension and plugins like show, etc.
*)
open GT

(* Opening a library for combinator-based syntax analysis *)
open Ostap
open Combinators
                         
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
    let enter st xs = {empty with g = st.g; scope = xs}

    (* Drops a scope *)
    let leave st st' = {st' with g = st.g}

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
    (* binary operator  *) | Binop of string * t * t 
    (* function call    *) | Call  of string * t list with show
    
    (* Available binary operators:
        !!                   --- disjunction
        &&                   --- conjunction
        ==, !=, <=, <, >=, > --- comparisons
        +, -                 --- addition, subtraction
        *, /, %              --- multiplication, division, reminder
    *)

    (* The type of configuration: a state, an input stream, an output stream, an optional value *)
    type config = State.t * int list * int list * int option
                                                            
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

          val eval : env -> config -> t -> config


       Takes an environment, a configuration and an expresion, and returns another configuration. The 
       environment supplies the following method

           method definition : env -> string -> int list -> config -> config

       which takes an environment (of the same type), a name of the function, a list of actual parameters and a configuration, 
       and returns the resulting configuration;
	   
	   ensureRetval() (same arguments) returns a pair: the configuration configuration and obligatory return value.
    *)
    
    let rec ensureRetval env conf expr =
      let (s, i, o, r) = eval env conf expr in (
        match r with
          | Some n -> (s, i, o, r), n
          | None -> failwith "[Stmt] A return value was expected whereas void was provided."
      )
    and eval env ((s, i, o, r) as conf) (expr:t) = 
      match expr with
      | Const n          -> (s, i, o, Some n)
      | Var   x          -> (s, i, o, Some (State.eval s x))
      | Binop(op, x, y)  ->
        let (conf, r1) = ensureRetval env conf x in
        let (conf, r2) = ensureRetval env conf y in
        (s, i, o, Some (to_func op r1 r2))
      | Call(name, args) ->
        let rec evalArgs conf args = match args with
          | [] -> conf, []
          | arg::args -> (
            let (s, i, o, r) = eval env conf arg in
            match r with
              | None -> failwith "[Expr] An argument provided to a function is void."
              | Some n ->
                let conf, argvals = evalArgs (s, i, o, r) args in
                conf, n::argvals
          )
        in
        let (conf, argvals) = evalArgs conf args in
        env#definition env name argvals conf
        
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
    (* call a procedure                 *) | Call   of string * Expr.t list
    (* return statement                 *) | Return of Expr.t option with show

    (* The type of configuration: a state, an input stream, an output stream *)
    type config = State.t * int list * int list 

    (* Statement evaluator

         val eval : env -> config -> t -> t -> config

       Takes an environment, a configuration, a statement and a residual statement, and returns another configuration. The 
       environment supplies the following method

           method definition : string -> (string list, string list, t)

       which returns a list of formal parameters and a body for given definition
    *)

    let rec eval env ((s, i, o, r) as conf) k (stmt:t) =
      if (stmt = Skip)
        then (
          if (k = Skip)
            then conf
            else eval env conf Skip k
        )
        else match stmt with
          | Read v ->
            (
              match i with
                | n::i -> (State.update v n s), i, o, None
                | _ -> failwith "[Stmt] No input for Read statement"
            )
          | Write x ->
            let ((s, i, o, r), n) = Expr.ensureRetval env conf x in 
            s, i, o @ [n], None
          | Assign(v, x) ->
            let ((s, i, o, r), n) = Expr.ensureRetval env conf x in
            (State.update v n s), i, o, None
          | Seq(t1, t2) -> 
            let conf = eval env conf k t1 in
            eval env conf k t2
          | If(cond, p1, p2) -> 
            let (conf, condVal) = Expr.ensureRetval env conf cond in
            if (condVal != 0) then eval env conf k p1 else eval env conf k p2
          | While(cond, body)  ->
            let (conf, condVal) = Expr.ensureRetval env conf cond in
            eval env conf k (if (condVal != 0) then Seq(body, While(cond, body)) else Skip)
          | Repeat(body, cond) ->
            let conf = eval env conf k body in
            let (conf, condVal) = Expr.ensureRetval env conf cond in
            eval env conf k (if (condVal = 0) then Repeat(body, cond) else Skip)
          | Call(name, args_provided) ->
            let conf = Expr.eval env conf (Expr.Call(name, args_provided)) in
            eval env conf k Skip
          | Return(Some t) ->
            let (conf, _) = Expr.ensureRetval env conf t in
            conf
          | Return(None) -> conf
          | _ -> failwith "[Stmt] Unsupported statement"
          
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
  let m          = List.fold_left (fun m ((name, _) as def) -> M.add name def m) M.empty defs in  
  let _, _, o, _ =
    Stmt.eval
      (object
         method definition env f args (st, i, o, r) =
           let xs, locs, s      = snd @@ M.find f m in
           let st'              = List.fold_left (fun st (x, a) -> State.update x a st) (State.enter st (xs @ locs)) (List.combine xs args) in
           let st'', i', o', r' = Stmt.eval env (st', i, o, r) Stmt.Skip s in
           (State.leave st'' st, i', o', r')
       end)
      (State.empty, i, [], None)
      Stmt.Skip
      body
  in
  o

(* Top-level parser *)
let parse = ostap (!(Definition.parse)* !(Stmt.parse))
