(* X86 codegeneration interface *)

(* The registers: *)
let regs = [|"%ebx"; "%ecx"; "%esi"; "%edi"; "%eax"; "%edx"; "%ebp"; "%esp"|]

(* We can not freely operate with all register; only 3 by now *)                    
let num_of_regs = Array.length regs - 5

(* We need to know the word size to calculate offsets correctly *)
let word_size = 4

(* We need to distinguish the following operand types: *)
type opnd = 
| R of int     (* hard register                    *)
| S of int     (* a position on the hardware stack *)
| M of string  (* a named memory location          *)
| L of int     (* an immediate operand             *)

(* For convenience we define the following synonyms for the registers: *)         
let ebx = R 0
let ecx = R 1
let esi = R 2
let edi = R 3
let eax = R 4
let edx = R 5
let ebp = R 6
let esp = R 7

(* Now x86 instruction (we do not need all of them): *)
type instr =
(* copies a value from the first to the second operand  *) | Mov   of opnd * opnd
(* makes a binary operation; note, the first operand    *) | Binop of string * opnd * opnd
(* designates x86 operator, not the source language one *)
(* x86 integer division, see instruction set reference  *) | IDiv  of opnd
(* see instruction set reference                        *) | Cltd
(* sets a value from flags; the first operand is the    *) | Set   of string * string
(* suffix, which determines the value being set, the    *)                     
(* the second --- (sub)register name                    *)
(* pushes the operand on the hardware stack             *) | Push  of opnd
(* pops from the hardware stack to the operand          *) | Pop   of opnd
(* call a function by a name                            *) | Call  of string
(* returns from a function                              *) | Ret
(* a label in the code                                  *) | Label of string
(* a conditional jump                                   *) | CJmp  of string * string
(* a non-conditional jump                               *) | Jmp   of string
(* directive                                            *) | Meta  of string
(* swap                                                 *) | Swap  of opnd * opnd
(* comment                                              *) | Comm  of string
                         
(* arithmetic correction: decrement                     *) | Dec   of opnd
(* arithmetic correction: or 0x0001                     *) | Or1   of opnd
(* arithmetic correction: shl 1                         *) | Sal1  of opnd
(* arithmetic correction: shr 1                         *) | Sar1  of opnd
                         
(* Instruction printer *)
let printInstr instr =
  let binop = function
  | "+"   -> "addl"
  | "-"   -> "subl"
  | "*"   -> "imull"
  | "&&"  -> "andl"
  | "!!"  -> "orl" 
  | "^"   -> "xorl"
  | "cmp" -> "cmpl"
  | _     -> failwith "[X86] Unknown binary operator"
  in
  let opnd = function
  | R i -> regs.(i)
  | S i -> if i >= 0
           then Printf.sprintf "-%d(%%ebp)" ((i+1) * word_size)
           else Printf.sprintf "%d(%%ebp)"  (8+(-i-1) * word_size)
  | M x -> x
  | L i -> Printf.sprintf "$%d" i
  in
  match instr with
  | Cltd               -> "\tcltd"
  | Set   (suf, s)     -> Printf.sprintf "\tset%s\t%s"     suf s
  | IDiv   s1          -> Printf.sprintf "\tidivl\t%s"     (opnd s1)
  | Binop (op, s1, s2) -> Printf.sprintf "\t%s\t%s,\t%s"   (binop op) (opnd s1) (opnd s2)
  | Mov   (s1, s2)     -> Printf.sprintf "\tmovl\t%s,\t%s" (opnd s1) (opnd s2)
  | Push   s           -> Printf.sprintf "\tpushl\t%s"     (opnd s)
  | Pop    s           -> Printf.sprintf "\tpopl\t%s"      (opnd s)
  | Ret                -> "\tret"
  | Call   p           -> Printf.sprintf "\tcall\t%s" p
  | Label  l           -> Printf.sprintf "%s:\n" l
  | Jmp    l           -> Printf.sprintf "\tjmp\t%s" l
  | CJmp  (s , l)      -> Printf.sprintf "\tj%s\t%s" s l
  | Meta   s           -> Printf.sprintf "%s\n" s
  | Swap  (s1, s2)     -> Printf.sprintf "\txchgl\t%s,\t%s"   (opnd s1) (opnd s2)
  | Comm   s           -> Printf.sprintf "#%s" s
  | Dec    s           -> Printf.sprintf "\tdecl\t%s"      (opnd s)
  | Or1    s           -> Printf.sprintf "\torl \t$0x0001,\t%s" (opnd s)
  | Sal1   s           -> Printf.sprintf "\tsall\t%s"      (opnd s)
  | Sar1   s           -> Printf.sprintf "\tsarl\t%s"      (opnd s)
  
(* A set of strings *)           
module S = Set.Make (String)

(* A map indexed by strings *)
module M = Map.Make (String) 

(* Environment implementation *)
let make_assoc l st_val = List.combine l (List.init (List.length l) (fun x -> x + st_val))
                    
let rec printList l = (match l with
  | [] -> Printf.printf "\n"
  | [(a, _)] -> Printf.printf "%s\n" a
  | (a, _)::l -> (Printf.printf "%s, " a; printList l)
)
                    
class env =
  let chars          = "_abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNJPQRSTUVWXYZ" in
  let rec assoc  x   = function [] -> raise Not_found | l :: ls -> try List.assoc x l with Not_found -> assoc x ls in
  object (self)
    val globals     = S.empty (* a set of global variables         *)
    val stringm     = M.empty (* a string map                      *)
    val scount      = 0       (* string count                      *)
    val stack_slots = 0       (* maximal number of stack positions *)
    val static_size = 0       (* static data size                  *)
    val stack       = []      (* symbolic stack                    *)
    val args        = []      (* function arguments                *)
    val locals      = []      (* function local variables          *)
    val fname       = ""      (* function name                     *)
    
    (*  
    method dump = (
      Printf.printf "DUMP %s\n" fname;
      Printf.printf "stack slots: %d\n" stack_slots;
      Printf.printf "arguments:   "; printList args;
      Printf.printf "locals:      "; printList locals
    )
    *)  
    (* gets a name for a global variable *)
    method loc x =
      try S (- (List.assoc x args)  -  1)
      with Not_found ->  
        try S (assoc x locals) with Not_found -> M ("global_" ^ x)
        
    (* allocates a fresh position on a symbolic stack *)
    method allocate =    
      let x, n =
        let rec allocate' = function
          | []                            -> ebx     , 0
          | (S n)::_                      -> S (n+1) , n+2
          | (R n)::_ when n < num_of_regs -> R (n+1) , stack_slots
		  | _                             -> S static_size, static_size+1
        in
        allocate' stack
      in
      x, {< stack_slots = max n stack_slots; stack = x::stack >}

	method size = List.length stack
	  
    (* pushes an operand to the symbolic stack *)
    method push y = {< stack = y::stack >}

    (* pops one operand from the symbolic stack *)
    method pop = match stack with
      | x::stack' -> x, {< stack = stack' >}
      | _ -> failwith "[X86] Empty stack."
      
    (* pops two operands from the symbolic stack *)
    method pop2 = match stack with
      | x::y::stack' -> x, y, {< stack = stack' >}
      | _ -> failwith "[X86] Not enough values on the stack."
	  
	(* peeks the top of the stack (the stack does not change) *)
	method peek = List.hd stack

	(* tag hash: gets a hash for a string tag *)
    method hash tag =
      let h = Pervasives.ref 0 in
      for i = 0 to min (String.length tag - 1) 4 do
        h := (!h lsl 6) lor (String.index chars tag.[i])
      done;
      !h      
	  
    (* registers a global variable in the environment *)
    method global x  = {< globals = S.add ("global_" ^ x) globals >}

    (* gets all global variables *)      
    method globals = S.elements globals

    (* gets a number of stack positions allocated *)
    method allocated = stack_slots                                
                                
    (* enters a function *)
    method enter f a l =
	  let n = List.length l in
      {< static_size = n; stack_slots = n; stack = []; locals = [make_assoc l 0]; args = make_assoc a 0; fname = f >}

	(* enters a scope *)
    method scope vars =
      let n = List.length vars in
      let static_size' = n + static_size in
      {< stack_slots = max stack_slots static_size'; static_size = static_size'; locals = (make_assoc vars static_size) :: locals >}

    (* leaves a scope *)
    method unscope =
      let n = List.length (List.hd locals) in
      {< static_size = static_size - n; locals = List.tl locals >}
	  
    (* returns a label for the epilogue *)
    method epilogue = Printf.sprintf "%s_epilogue" fname
                                     
    (* returns a name for local size meta-symbol *)
    method lsize = Printf.sprintf "%s_SIZE" fname

    (* returns a list of live registers *)
    method live_registers =
      List.filter (function R _ -> true | _ -> false) stack

    (* registers a string constant *)
    method string x =
      try M.find x stringm, self
      with Not_found ->
        let y = Printf.sprintf "string_%d" scount in
        let m = M.add x y stringm in
        y, {< scount = scount + 1; stringm = m>}
        
    (* gets all string definitions *)      
    method strings = M.bindings stringm
      
  end
  
(* Opening stack machine to use instructions without fully qualified names *)
open SM

(* Opening language to use values *)
open Language

(* Single instruction compilation

     compileInstr : env -> prg -> env * instr list

   Take an environment, a stack machine program, and returns a pair --- the updated environment and the list
   of x86 instructions
*)

let inRegister x = match x with
  | R _ -> true
  | _ -> false

let inMemory x = match x with
  | S _ | M _ -> true
  | _ -> false
	  
let compSuffix op = match op with
  | "<"  -> "lb"
  | "<=" -> "leb"
  | ">"  -> "gb"
  | ">=" -> "geb"
  | "==" -> "eb"
  | "!=" -> "neb"
  | _    -> failwith "[X86] Unsupported comparator"
  
let zeroOut reg = Binop("^", reg, reg)

let movImpl a b = 
  if (a = b) then []
  else
    if (inMemory a) && (inMemory b)
      then [Mov (a, eax); Mov (eax, b)]
      else [Mov (a, b)]

(* Like a half of this is mostly pointless and assumes there will be some eax-related optimizations down the line *)
let rec swapImpl a b =
  if (a = b) then []
  else
    if (inRegister a) && (inRegister b)
	  then [Swap (a, b)]
	  else
	    if (inRegister a)
		  then [Mov(b, eax)] @ swapImpl a eax @ [Mov(eax, b)]
		  else
		    if (inRegister b)
		      then [Mov(a, eax)] @ swapImpl b eax @ [Mov(eax, a)]
			  else
			    let xor a b = [Binop("^", a, b)] in
				xor eax eax @ xor a eax @ xor b eax @ xor eax a @ xor eax b

let unbox x = [Sar1 (x)]
let box x = [Sal1 x; Or1 x]

let rec split env acc = function
  | 0 -> env, acc
  | n -> let x, env = env#pop in split env (x :: acc) (n - 1)

let rec compileCall env name arg_amount arg_prepushed prelude hasRetval =
  let env, push = split env [] arg_amount in
  let push = List.map (fun x -> Push x) push in
  let s = List.map (fun x -> Push x) env#live_registers in
  let r = List.rev (List.map (fun x -> Pop x) env#live_registers) in
  let env, code = env, s @ push @ prelude @ [Call name; Binop ("+", L ((arg_amount + arg_prepushed) * word_size), esp)] @ r in
  if hasRetval
    then let rv, env = env#allocate in env, code @ [Mov (eax, rv)]
    else env, code
  
and compileInstr (env:env) i =
  let slots_before = Printf.sprintf "%d" (env#size) in
  let env, code = match i with
  | CONST n ->
    let a, env = env#allocate in
    env, [Mov (L (n * 2 + 1), a)]
  | LD v ->
    let s, env = (env#global v)#allocate in
    env, movImpl (env#loc v) s
  | ST v ->
    let s, env = (env#global v)#pop in
    env, movImpl s (env#loc v)
  | STA (x, n) ->
    let prelude = [Push (L n); Push (env#loc x)] in
    let env, code = compileCall env "Bsta" (n + 1) 2 prelude false in
    env, code
  | STRING s ->
    let s, env = env#string s in
    let env, code = compileCall env "Bstring" 0 1 [Push (M ("$" ^ s));] true in
    (env, code)
  | LABEL label -> env, [Label label]
  | JMP label -> env, [Jmp label]
  | CJMP(needZero, label) ->
    let s, env = env#pop in
    env, [Binop("cmp", L 1, s); CJmp(needZero, label)]
  | END ->
    env,
    [
      Label env#epilogue; Mov (ebp, esp); Pop ebp; Ret;
      Meta (Printf.sprintf "\t.set %s, %d" env#lsize (env#allocated * word_size))
    ]
  | RET false -> env, [Jmp env#epilogue]
  | RET true  ->
    let retval, prev_env = env#pop in
    prev_env, [Mov (retval, eax); Jmp env#epilogue]
(*  | CALL(name, arg_amount, hasRetval) -> compileCall env name arg_amount 0 [] hasRetval*)
  | BEGIN(f, args, locs)  ->
    let env = env#enter f args locs in
    env, [Push ebp; Mov (esp, ebp); Binop ("-", M ("$" ^ env#lsize), esp)]
  | DUP ->
    let a = env#peek in
	let b, env = env#allocate in
	env, movImpl a b
  | SWAP ->
    let _, _, env = env#pop2 in
	let a, env = env#allocate in
	let b, env = env#allocate in
	env, swapImpl a b
  | DROP -> let _, env = env#pop in env, []
  | TAG tag ->
    let tag = env#hash tag in
	let prelude = [Push (L tag)] in
	let env, code = compileCall env "Btag" 1 1 prelude true in
	(env, code)
  | LEAVE -> let _, env = (env#unscope)#allocate in env, []
  | ENTER vars ->
    let env = env#scope vars in
    let env, vals = split env [] (List.length vars) in
	env,
	List.concat (List.map
	  (fun (vr, vl) -> movImpl vl (env#loc vr))
	  (List.combine vars (List.rev vals))
	)
  | SEXP (tag, n) ->
    let tag = env#hash tag in
	compileCall env "Bsexp" n 2 [Push (L n); Push (L tag)] true
  | BINOP op -> (
    let b, a, env = env#pop2 in
    match op with
      | "+" ->
        let env, code = if inRegister a
          then env#push a, [Binop(op, b, a)]
          else (
            if inRegister b
              then env#push b, [Binop(op, a, b)]
              else env#push a, [Mov(a, eax); Binop(op, b, eax); Mov(eax, a)]
            )
        in env, (Dec (b)) :: code
      | "-" ->
        env#push a, (Dec (b)) ::
        if inRegister a
          then [Binop(op, b, a)]
          else [Mov(a, eax); Binop(op, b, eax); Mov(eax, a)]
      | "*" ->
        let env, code = if inRegister a
          then env#push a, [Binop(op, b, a)] @ box a
          else (
            if inRegister b
              then env#push b, [Binop(op, a, b)] @ box b
              else env#push a, [Mov(a, eax); Binop(op, b, eax); Mov(eax, a)] @ box a
          )
        in env, unbox b @ unbox a @ code
      | "/" | "%" -> 
        let result = match op with
          | "/" -> eax
          | _ -> edx
        in
        env#push a, unbox a @ unbox b @ [Mov(a, eax); Cltd; IDiv b] @ box result @ [Mov (result, a)]
      | "&&" | "!!" ->
        env#push a, [
          zeroOut eax; zeroOut edx;
          Binop ("cmp", L 1, a); Set ("neb", "%al");
          Binop ("cmp", L 1, b); Set ("neb", "%dl");
          Binop (op, eax, edx)
        ] @ box edx @ [Mov (edx, a)]
      | "<" | "<=" | ">" | ">=" | "==" | "!=" ->
        (* Optimizable with regards to second operand *)
        env#push a,
        (if inRegister a
          then [zeroOut eax; Binop ("cmp", b, a)]
          else [zeroOut eax; Mov (a, edx); Binop ("cmp", b, edx)]
        ) @ [Set(compSuffix op, "%al")] @ box eax @ [Mov (eax, a)] 
      | _ -> failwith "[X86] Unsupported binary operator"
  ) in
  let slots_after = Printf.sprintf "%d" (env#size) in
  env, [Comm ((GT.transform(insn) new @insn[show] () i) ^ " " ^ slots_before ^ " -> " ^ slots_after)] @ code
  (*in env, code*)
  (*| _ -> failwith (Printf.sprintf "[X86] Unimplemented instruction: %s" (GT.transform(insn) new @insn[show] () i))*)
    
(* Symbolic stack machine evaluator

     compile : env -> prg -> env * instr list

   Take an environment, a stack machine program, and returns a pair --- the updated environment and the list
   of x86 instructions
*)

let rec compile env p =
  match p with
    | [] -> env, []
    | i::p ->
        let env, x86p1 = compileInstr env i in
        let env, x86p2 = compile env p in
        env, x86p1 @ x86p2
  
(* Generates an assembler text for a program: first compiles the program into
   the stack code, then generates x86 assember code, then prints the assembler file
*)
let genasm (ds, stmt) =
  let stmt = Language.Stmt.Seq (stmt, Language.Stmt.Return (Some (Language.Expr.Call ("Lraw", [Language.Expr.Const (Language.Value.Int 0)])))) in
  let env, code =
    compile
      (new env)
      ((LABEL "main") :: (BEGIN ("main", [], [])) :: SM.compile (ds, stmt))
  in
  let data = Meta "\t.data" ::
    (List.map (fun s      -> Meta (Printf.sprintf "%s:\t.int\t0"           s)) env#globals) @
    (List.map (fun (s, v) -> Meta (Printf.sprintf "%s:\t.string\t\"%s\"" v s)) env#strings) in 
  let asm = Buffer.create 1024 in
  List.iter
    (fun i -> Buffer.add_string asm (Printf.sprintf "%s\n" @@ printInstr i))
    (data @ [Meta "\t.text"; Meta "\t.globl\tmain"] @ code);
  Buffer.contents asm

(* Builds a program: generates the assembler file and compiles it with the gcc toolchain *)
let build prog name =
  let outf = open_out (Printf.sprintf "%s.s" name) in
  Printf.fprintf outf "%s" (genasm prog);
  close_out outf;
  let inc = try Sys.getenv "RC_RUNTIME" with _ -> "../runtime" in
  Sys.command (Printf.sprintf "gcc -gstabs+ -m32 -o %s %s/runtime.o %s.s" name inc name)