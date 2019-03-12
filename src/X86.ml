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
    
(* A set of strings *)           
module S = Set.Make (String)

(* Environment implementation *)
let make_assoc l = List.combine l (List.init (List.length l) (fun x -> x))
                    
let rec printList l = (match l with
  | [] -> Printf.printf "\n"
  | [(a, _)] -> Printf.printf "%s\n" a
  | (a, _)::l -> (Printf.printf "%s, " a; printList l)
)
                    
class env =
  object (self)
    val globals     = S.empty (* a set of global variables         *)
    val stack_slots = 0       (* maximal number of stack positions *)
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
        try S (List.assoc x locals) with Not_found -> M ("global_" ^ x)
        
    (* allocates a fresh position on a symbolic stack *)
    method allocate =    
      let x, n =
        let rec allocate' = function
          | []                            -> ebx     , 0
          | (S n)::_                      -> S (n+1) , n+1
          | (R n)::_ when n < num_of_regs -> R (n+1) , stack_slots
          | (M _)::s                      -> allocate' s
          | _                             -> S 0     , 1
        in
        allocate' stack
      in
      x, {< stack_slots = max n stack_slots; stack = x::stack >}

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

    (* registers a global variable in the environment *)
    method global x  = {< globals = S.add ("global_" ^ x) globals >}

    (* gets all global variables *)      
    method globals = S.elements globals

    (* gets a number of stack positions allocated *)
    method allocated = stack_slots                                
                                
    (* enters a function *)
    method enter f a l =
      {< stack_slots = List.length l; stack = []; locals = make_assoc l; args = make_assoc a; fname = f >}

    (* returns a label for the epilogue *)
    method epilogue = Printf.sprintf "L%s_epilogue" fname
                                     
    (* returns a name for local size meta-symbol *)
    method lsize = Printf.sprintf "L%s_SIZE" fname

    (* returns a list of live registers *)
    method live_registers =
      List.filter (function R _ -> true | _ -> false) stack
      
  end
  
(* Opening stack machine to use instructions without fully qualified names *)
open SM

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

let movImpl a b = 
  if (a = b) then []
  else
    if (inMemory a) && (inMemory b)
      then [Mov (a, eax); Mov (eax, b)]
      else [Mov (a, b)]

let compSuffix op = match op with
  | "<"  -> "l"
  | "<=" -> "le"
  | ">"  -> "g"
  | ">=" -> "ge"
  | "==" -> "e"
  | "!=" -> "ne"
  | _    -> failwith "[X86] Unsupported comparator"
  
let zeroOut reg = Binop("^", reg, reg)
   
let compileInstr (env:env) i =
  match i with
  | BINOP op -> (
    let b, a, env = env#pop2 in
    match op with
      | "+" | "-" | "*" ->
        if inRegister a
          then env#push a, [Binop(op, b, a)]
          else (
            if inRegister b
              then env#push b, [Binop(op, a, b)]
              else env#push a, [Mov(a, eax); Binop(op, b, eax); Mov(eax, a)]
        )
      | "/" | "%" -> 
        let result = match op with
          | "/" -> eax
          | _ -> edx
        in
        env#push a, [Mov(a, eax); Cltd; IDiv b; Mov (result, a)]
      | "&&" | "!!" ->
        (*This one could be optimised a bit*)
        env#push a, [
          zeroOut eax; zeroOut edx;
          Binop ("cmp", L 0, a); Set ("nz", "%al");
          Binop ("cmp", L 0, b); Set ("nz", "%dl");
          Binop (op, eax, edx); Mov (edx, a)
        ]
      | "<" | "<=" | ">" | ">=" | "==" | "!=" ->
        env#push a,
        if inRegister a
          then [zeroOut eax; Binop ("cmp", b, a); Set(compSuffix op, "%al"); Mov (eax, a)] 
          else [zeroOut eax; Mov (a, edx); Binop ("cmp", b, edx); Set (compSuffix op, "%al"); Mov (eax, a)]
      | _ -> failwith "[X86] Unsupported binary operator"
  )
  | CONST n ->
    let a, env = env#allocate in
    env, [Mov (L n, a)]
  | LD v ->
    let s, env = (env#global v)#allocate in
    env, movImpl (env#loc v) s
  | ST v ->
    let s, env = (env#global v)#pop in
    env, movImpl s (env#loc v)
  | LABEL label -> env, [Label label]
  | JMP label -> env, [Jmp label]
  | CJMP(needZero, label) ->
    let s, env = env#pop in
    env, [Binop("cmp", L 0, s); CJmp(needZero, label)]
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
  | CALL(name, arg_amount, _) -> 
    let rec push env' acc = function
      | 0 -> env', acc
      | n -> let x, env' = env'#pop in push env' (Push x :: acc) (n - 1)
    in
    let env, push = push env [] arg_amount in
    let s = List.map (fun x -> Push x) env#live_registers in
    let r = List.rev (List.map (fun x -> Pop x) env#live_registers) in
    let an, env = env#allocate in
    env, s @ push @ [Call name; Mov (eax, an); Binop ("+", L (arg_amount * word_size), esp)] @ r
  | BEGIN(f, args, locs)  ->
    let env = env#enter f args locs in
    env, [Push ebp; Mov (esp, ebp); Binop ("-", M ("$" ^ env#lsize), esp)]
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
  let stmt = Language.Stmt.Seq (stmt, Language.Stmt.Return (Some (Language.Expr.Const (Language.Value.Int 0)))) in
  let env, code =
    compile
      (new env)
      ((LABEL "main") :: (BEGIN ("main", [], [])) :: SM.compile (ds, stmt))
  in
  let data = Meta "\t.data" :: (List.map (fun s -> Meta (s ^ ":\t.int\t0")) env#globals) in 
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
  Sys.command (Printf.sprintf "gcc -m32 -o %s %s/runtime.o %s.s" name inc name)