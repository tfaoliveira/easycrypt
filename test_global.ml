open Map

(* 

type mem =
  | Mid of mident * memtype          (* m *)
  | Mrestr of mem * set              (* m|s *)
  | Mupd_var of mem * var * form     (* m[x<-f] *)
  | Mupd_set of mem * set * mem      (* m[s<-mid] *)

and form = 
| Fmem of mem
| Fpvar of mem * var

***************************************

To quantify over modified variable 
forall m', f[m <- Mupd_set(m, mod, m')]

***************************************
Simplification rules 

m[x<-f][x]  -> f 
m[x<-f][y]  -> m[y]   if x <> y
m[s<-m'][y] -> mid[y] if (x in s)
m[s<-m'][y] -> m[y]   if !(x in s)
(m|s)[y] -> m[y]      // no need to check if the formula is well typed 

(m|s1)|s2 -> (m|s1 inter s2)
(m|s1)[x<-f] -> m|s1   if !(x in s)
(m|s1)[x<-f] -> m[x<-f]|s1  otherwhise
(m|s1)[s<-m'] -> m|s1   if !(s disjoint s')
(m|s1)[s<-m'] -> m[s<-m']|s1  otherwhise

***************************

forall x:var, x \in set m1 => m1[x] = m2[x]
-------------------------------------------
           m1 = m2 
problem: what is the type of m1[x] and m2[x]?

********************************************

Typing rule:

ty = 
 | ty_mem of set


the type of memory is a set
a memory of type s1 can be view as a memory of type s2 if s2 incl s1

|- m : s     x in s
---------------------
  |- m[x] : x_ty

|- m : s1    s incl s1
---------------------
    |- m|s : s 

|- m : s   |- f : x_ty   x \in s
---------------------------------
     |- m[x<-f] : s 

|- m : s   |- m' : s'    s' incl s
-------------------------------------  
   |- m[s' <- m'] : s 


variant 
|- m : s   |- m' : s'    
-------------------------
   |- m[s' <- m'] : s U s'   
in that case the reduction for m[s' <- m'] need to be adapted.
advantage it allows to perform union of mem


In particular 
   (m|s1)[s<-m'] -> m[s<-m']|s1  otherwhise 
is not true anymore 

but 
  (m|s1)[s<-m'] -> m[s<-m'] | s1 U s'\s1

memtype = { global : set; local : ty Mident.t }
 

(m1[s<-m1']|s1) = m --> m1|s1\s = m|s1\s /\ m1'|s I s1 = m2'| s I s2


*******************************************
| Empty
| All (* The full set of global variable *)
| Singleton of variable
| Adv of (adv * oracle list)
| Union of set * set 
| Diff of set * set 
| Inter of set * set

(s1 U s2) I s = (s1 I s) U (s2 I s)
(s1 U s2) \ s = (s1 \ s) U (s2 \ s)



*)







type variable = string 
type adv = string 
type oracle = string 

type set = 
| Empty
| All (* The full set of global variable *)
| Singleton of variable
| Adv of (adv * oracle list)
| Union of set * set 
| Diff of set * set 
| Inter of set * set

let rec pp_list s pp_e fmt l = 
  match l with 
  | [] -> ()
  | [x] -> pp_e fmt x
  | x::l -> Format.fprintf fmt "%a%s%a" pp_e x s (pp_list s pp_e) l

let rec pp_set fmt = function
  | Empty -> Format.fprintf fmt "0"
  | All   -> Format.fprintf fmt "All"
  | Singleton x -> Format.fprintf fmt "{%s}" x
  | Adv(a,ol) -> 
    Format.fprintf fmt "%s(%a)" a (pp_list "," (fun fmt o -> Format.fprintf fmt "%s" o)) ol
  | Union (s1,s2) -> Format.fprintf fmt "(%a U %a)" pp_set s1 pp_set s2
  | Diff  (s1,s2) -> Format.fprintf fmt "(%a \ %a)" pp_set s1 pp_set s2
  | Inter (s1,s2) -> Format.fprintf fmt "(%a I %a)" pp_set s1 pp_set s2

module Mset = Map.Make (struct type t = set      let compare = compare end)
module Mvar = Map.Make (struct type t = variable let compare = compare end)
module Madv = Map.Make (struct type t = adv * oracle list let compare = compare end)

type meta = int
module Mmeta = Map.Make (struct type t = meta let compare = compare end)

type meta_var = 
  | Meta of meta
  | Var  of variable

let pp_mv fmt = function
  | Meta i -> Format.fprintf fmt "%%%i" i
  | Var x -> Format.fprintf fmt "%s" x

type mem = 
  { sign : bool
  ; var  : meta_var
  ; set  : set }
    
let mem sign (var:meta_var) (set:set) = 
  { sign; var; set }

let pp_mem fmt r = 
  Format.fprintf fmt "%a %s %a" pp_mv r.var (if r.sign then "in" else "nin") pp_set r.set

type meta_state = 
  { value : variable option 
  ; mem   : bool Mset.t }

type var_state = 
  bool Madv.t

let empty_var_state = 
  Madv.empty

let empty_meta_state = 
  { value = None
  ; mem = Mset.empty } 
  
type global_state = 
  { adv_incl : adv -> set
  ; orcl_def : oracle -> set }

type local_state = 
  { next : meta   
  ; var  : var_state Mvar.t
  ; meta : meta_state Mmeta.t 
  ; todo : mem list
  ; unsat : bool }  (* true means unsat; false unknown *)

let empty_local_state = 
  { next = 0
  ; var = Mvar.empty
  ; meta = Mmeta.empty
  ; todo = []
  ; unsat = false
  }

let fresh_meta st = 
  let next = st.next in
  next, { st with next = next + 1 }

let oget = function Some x -> x | None -> raise Not_found

let find_meta (st:local_state) (m:meta) = 
  Option.value (Mmeta.find_opt m st.meta) ~default:empty_meta_state

let find_var (st:local_state) (m:variable) = 
  Option.value (Mvar.find_opt m st.var) ~default:empty_var_state

let norm (st:local_state) mv = 
  match mv with 
  | Var _ -> mv
  | Meta m -> 
      try Var (oget (Mmeta.find m st.meta).value)
      with Not_found -> mv
 
let set_unsat unsat st = 
  { st with unsat = st.unsat || unsat}

exception SAT of local_state 

let push (st:local_state) r = 
  { st with todo = r :: st.todo }

let pushs (st:local_state) rs = 
  { st with todo = List.rev_append rs st.todo } 

let add_meta (st:local_state) m ms = 
  { st with meta = Mmeta.add m ms st.meta } 

(* Precondition m.value = None *)
let set_eq sign (m:meta) (v:variable) (st:local_state) = 
  let ms = find_meta st m in
  assert (ms.value = None);
  if sign then 
    let todo = 
      Mset.fold (fun s sign todo -> {sign; var = Var v; set = s} :: todo) ms.mem [] in
    let ms = { value = Some v; mem = Mset.empty } in
    let st = add_meta st m ms in 
    pushs st todo
  else 
    try 
      let b = Mset.find (Singleton v) ms.mem in
      set_unsat b st 
    with Not_found ->
      let ms = { ms with mem = Mset.add (Singleton v) false ms.mem } in
      add_meta st m ms 

let rec set_mem sign mv a st = 
  match mv with
  | Var x -> 
    let vs = find_var st x in
    begin match Madv.find a vs with
    | sign' -> set_unsat (sign <> sign') st
    | exception Not_found ->
      let vs = Madv.add a sign vs in
      { st with var = Mvar.add x vs st.var }
    end
  | Meta m ->
    let ms = find_meta st m in
    begin match ms.value with
    | Some x -> set_mem sign (Var x) a st
    | None -> 
      begin match Mset.find (Adv a) ms.mem with 
      | sign' -> set_unsat (sign <> sign') st
      | exception Not_found -> 
        let ms = { value = None; mem = Mset.add (Adv a) sign ms.mem } in
        add_meta st m ms
      end
    end    

let sup_adv gs a = gs.adv_incl a 
let sup_orcl gs o = gs.orcl_def o

let sup gs a ol = 
  List.fold_left (fun s o -> Union(s, sup_orcl gs o)) (sup_adv gs a) ol

let add_adv (gs:global_state) sign mv a ol (st:local_state) = 
  let st = set_mem sign mv (a,ol) st in
  if sign then 
    (* x in a(ol) -> x in sup a(ol) *)
    let sup = sup gs a ol in
    push st (mem true mv sup) 
  else 
    set_mem sign mv (a,[]) st 

let rec solve (gs:global_state) (st:local_state) = 
  if st.unsat then (Format.printf "UNSAT@."; ())
  else match st.todo with
  | [] -> raise (SAT st)
  | r :: todo -> 
    process gs r {st with todo}

(* precondition st.unsat = false *)
and process (gs:global_state) (r:mem) (st:local_state) = 
  Format.printf "process %a@." pp_mem r;
  let sts = 
    match r.set with
    | Empty -> [set_unsat r.sign st]
    | All   -> [set_unsat (not r.sign) st]
    | Singleton v ->
      begin match norm st r.var with
      | Meta m -> [set_eq r.sign m v st]  (* add the fact that m =sign v *)
      | Var v' -> 
        Format.printf "add %s %s %s (%s)@."  
           v (if r.sign then "=" else "<>") v' (if ((v = v') <> r.sign) then "unsat" else "sat");
        [set_unsat ((v = v') <> r.sign) st]
      end
    | Adv(a, ol) -> [add_adv gs r.sign r.var a ol st]
    | Union (s1,s2) -> 
      let r1 = { r with set = s1 } in
      let r2 = { r with set = s2 } in
      if r.sign then 
        (* mv in s1 U s2 = mv in s1 || mv in s2 *)
        [push st r1; push st r2]
       else
         (* !(mv in s1 U s2) = !(mv in s1) && !(mv in s2) *)
         [pushs st [r1; r2]]
     | Diff (s1, s2) ->
       let r1 = { r with set = s1 } in
       let r2 = { r with sign = not r.sign; set = s2 } in
       if r.sign then 
         (* mv in s1 \ s2 = mv in s1 && !mv in s2 *)
         [pushs st [r1; r2]]
       else
         (* !(mv in s1 \ s2) = !(mv in s1) || mv in s2 *)
         [push st r1; push st r2]
     | Inter (s1, s2) ->
       let r1 = { r with set = s1 } in  
       let r2 = { r with set = s2 } in  
       if r.sign then 
         (* mv in s1 inter s2 = mv in s1 && mv in s2 *)
         [pushs st [r1; r2]]
       else
         (* !(mv in s1 inter s2) = !(mv in s1) || !(mv in s2) *)
         [push st r1; push st r2] 
  in
  List.iter (solve gs) sts

let disjoint gs s1 s2 = 
  (* add clause !((s1 inter s2) subset 0) 
     -----------------------------------
     x in s1 inter s2 && !(x in 0) 
     -----------------------------------
     x in s1 && x in s2
  *)
  let st = empty_local_state in
  let m, st = fresh_meta st in  
  let st = pushs st [mem true (Meta m) (Inter(s1, s2))] in
  solve gs st
      
let is_mem gs sign x s = 
  let st = empty_local_state in
  let st = push st (mem (not sign) (Var x) s) in
  solve gs st


(* tests *)

let x = "x"
let y = "y"
let z = "z"
let _A = "A"
let _B = "B"

let init_gs advs orcls = 
  { adv_incl = (fun a -> try List.assoc a advs with Not_found -> All)
  ; orcl_def = fun o -> try List.assoc o orcls with Not_found -> Empty }


let _ = 
  Format.printf "A : All \ B; B: All; disjoint A B@.";
  let gs = init_gs [_A, Diff(All, Adv(_B,[])); _B, All] 
                    [] in
  try 
    disjoint gs (Adv(_A,[])) (Adv(_B,[]));           
    Format.printf "ok@."
  with SAT _ ->
    Format.printf "SAT@."

let _ = 
  Format.printf "A : All \ B; B: All; disjoint A A@.";
  let gs = init_gs [_A, Diff(All, Adv(_B,[])); _B, All] 
                    [] in
  try 
    disjoint gs (Adv(_A,[])) (Adv(_B,[]));           
    Format.printf "ok@."
  with SAT _ ->
    Format.printf "SAT@."



let _ = 
    Format.printf "A : All \ B; B: All; x in A U {x, y} @.";
  let gs = init_gs [_A, Diff(All, Union(Adv(_B,[]), Singleton x)); _B, All] 
                   [] in
  try is_mem gs true x (Union (Adv(_A, []), Union(Singleton x, Singleton y)));
      Format.printf "ok@."
  with SAT _ ->
    Format.printf "SAT@."
                       

