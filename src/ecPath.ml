(* -------------------------------------------------------------------- *)
open EcUtils
open EcMaps
open EcSymbols
open EcIdent

(* -------------------------------------------------------------------- *)
(** {2 Path} *)

type path = {
  p_node : path_node;
  p_tag  : int
}

and path_node =
| Psymbol of symbol
| Pqname  of path * symbol

(* -------------------------------------------------------------------- *)
let p_equal   = ((==) : path -> path -> bool)
let p_hash    = fun p -> p.p_tag
let p_compare = fun p1 p2 -> p_hash p1 - p_hash p2

module Hspath = Why3.Hashcons.Make (struct
  type t = path

  let equal_node p1 p2 =
    match p1, p2 with
    | Psymbol id1, Psymbol id2 ->
        sym_equal id1 id2
    | Pqname (p1, id1), Pqname(p2, id2) ->
        sym_equal id1 id2 && p_equal p1 p2
    | _ -> false

  let equal p1 p2 = equal_node p1.p_node p2.p_node

  let hash p =
    match p.p_node with
    | Psymbol id    -> Hashtbl.hash id
    | Pqname (p,id) -> Why3.Hashcons.combine p.p_tag (Hashtbl.hash id)

  let tag n p = { p with p_tag = n }
end)

module Path = MakeMSH (struct
  type t  = path
  let tag = p_hash
end)

let rec p_ntr_compare (p1 : path) (p2 : path) =
  match p1.p_node, p2.p_node with
  | Psymbol _, Pqname  _ -> -1
  | Pqname  _, Psymbol _ -> +1

  | Psymbol x1, Psymbol x2 ->
       String.compare x1 x2

  | Pqname (p1, x1), Pqname (p2, x2) -> begin
      match p_ntr_compare p1 p2 with
      | 0 -> String.compare x1 x2
      | n -> n
    end

(* -------------------------------------------------------------------- *)
module Mp = Path.M
module Hp = Path.H

module Sp = struct
  include Path.S

  let ntr_elements s =
    List.ksort ~key:identity ~cmp:p_ntr_compare (elements s)
end

(* -------------------------------------------------------------------- *)
let mk_path node =
  Hspath.hashcons { p_node = node; p_tag = -1; }

let psymbol id   = mk_path (Psymbol id)
let pqname  p id = mk_path (Pqname(p,id))

let rec pappend p1 p2 =
  match p2.p_node with
  | Psymbol id -> pqname p1 id
  | Pqname(p2,id) -> pqname (pappend p1 p2) id

let pqoname p id =
  match p with
  | None   -> psymbol id
  | Some p -> pqname p id

(* -------------------------------------------------------------------- *)
let rec tostring p =
  match p.p_node with
  | Psymbol x    -> x
  | Pqname (p,x) -> Printf.sprintf "%s.%s" (tostring p) x

let tolist =
  let rec aux l p =
    match p.p_node with
    | Psymbol x     -> x :: l
    | Pqname (p, x) -> aux (x :: l) p in
  aux []

let toqsymbol (p : path) =
  match p.p_node with
  | Psymbol x     -> ([], x)
  | Pqname (p, x) -> (tolist p, x)

let fromqsymbol ((nm, x) : qsymbol) =
  pqoname
    (List.fold_left
       (fun p x -> Some (pqoname p x)) None nm)
    x

let basename p =
  match p.p_node with
  | Psymbol x     -> x
  | Pqname (_, x) -> x

let extend p s =
  List.fold_left pqname p s

let prefix p =
  match p.p_node with
  | Psymbol _ -> None
  | Pqname (p, _) -> Some p

let rec getprefix_r acc p q =
  match p_equal p q with
  | true  -> Some acc
  | false ->
      match q.p_node with
      | Psymbol _     -> None
      | Pqname (q, x) -> getprefix_r (x::acc) p q

let getprefix p q = getprefix_r [] p q

let isprefix p q =
  match getprefix p q with
  | None   -> false
  | Some _ -> true

let rec rootname p =
  match p.p_node with
  | Psymbol x     -> x
  | Pqname (p, _) -> rootname p

let rec p_size p =
  match p.p_node with
  | Psymbol _     -> 1
  | Pqname (p, _) -> 1 + (p_size p)


(* -------------------------------------------------------------------- *)
(** {2 Module path} *)

type wrap_k = [`Ext | `Cb]

(** top-level module path: an ident (for abstract modules) or a concrete path *)
type mpath_core_top = [`Local of ident | `Concrete of path]

(** a core module path *)
type mpath_core_node =
  | Top  of mpath_core_top

  | App  of mpath_core * mpath list
  (** application, [App(mc,args)] is [mc(args)]
      applications are strict and maximally grouped, i.e. there are no
      - [App (_, [])]
      - [App (App (_,_), _)] *)

  | Wrap of ident * wrap_k * mpath_core
  (** [Wrap (a, `Ext, mc)] delegates the evaluation of [mc] to agent [a].
      [Wrap (a, `Cb , mc)] restores [mc] evaluation to [a]'s caller. *)

(** hashconsed [mpath_core_node] *)
and mpath_core = { c_cnt : mpath_core_node; c_tag : int }

(** a module path:
    - [{ core; sub = None   }] is [core].
    - [{ core; sub = Some p }] is [core.p]. *)
and mpath = {
  core  : mpath_core;
  sub   : path option;
  m_tag : int;                   (* hashconsing *)
}

(* -------------------------------------------------------------------- *)
let m_equal     = ((==) : mpath      -> mpath      -> bool)
let mcore_equal = ((==) : mpath_core -> mpath_core -> bool)

(* -------------------------------------------------------------------- *)
let mpath_core_top_equal (mt1 : mpath_core_top) (mt2 : mpath_core_top) =
  match mt1, mt2 with
  | `Local id1, `Local id2 -> EcIdent.id_equal id1 id2
  | `Concrete p1, `Concrete p2 -> p_equal p1 p2
  | _, _ -> false

let mpath_core_top_hash (mt : mpath_core_top) =
  match mt with
  | `Local id -> EcIdent.id_hash id
  | `Concrete p -> p_hash p

(* -------------------------------------------------------------------- *)
let mcore_hash (p : mpath_core) = p.c_tag
let mcore_compare (p1 : mpath_core) (p2 : mpath_core) =
  mcore_hash p1 - mcore_hash p2

(* -------------------------------------------------------------------- *)
let m_hash    (p : mpath)               = p.m_tag
let m_compare (p1 : mpath) (p2 : mpath) = m_hash p1 - m_hash p2

(* -------------------------------------------------------------------- *)
(** resolved top-level module path *)
type mpath_top_r =
  [ | `Local of ident
    | `Concrete of path * path option ]

(* -------------------------------------------------------------------- *)
(** {3 Module core path and path hashconsing} *)

(** Hasconsing of [mpath_core].
    Can assume that strict sub-terms are already hashconsed
    (either [path], [mpath], or [mpath_core]). *)
module Hsmpath_core = Why3.Hashcons.Make (struct
  type t = mpath_core

  let equal (m1 : t) (m2 : t) =
    match m1.c_cnt, m2.c_cnt with
    | Top t1, Top t2 -> mpath_core_top_equal t1 t2
    | App (c1, args1), App (c2,args2) ->
      mcore_equal c1 c2 && List.length args1 = List.length args2 &&
      List.for_all2 m_equal args1 args2

    | App _, Top _ | Top _, App _ -> false

  let hash (m : t) =
    match m.c_cnt with
    | Top t -> mpath_core_top_hash t
    | App (c,args) ->
      let hash = mcore_hash c in
      Why3.Hashcons.combine_list m_hash hash args

  let tag n (p : t) = { p with c_tag = n }
end)

(** Hasconsing of [mpath].
    Same assumptions as [Hsmpath_core]. *)
module Hsmpath = Why3.Hashcons.Make (struct
  type t = mpath

  let equal (m1 : t) (m2 : t) =
    mcore_equal m1.core m2.core && oeq p_equal m1.sub m2.sub

  let hash (m : t) =
    let hash  = mcore_hash m.core in
    let hash' = Why3.Hashcons.combine_option p_hash m.sub in
    Why3.Hashcons.combine hash hash'

  let tag n (p : t) = { p with m_tag = n }
end)

(* -------------------------------------------------------------------- *)
module MPath = MakeMSH (struct
  type t  = mpath
  let tag = m_hash
end)

module MCPath = MakeMSH (struct
  type t  = mpath_core
  let tag = mcore_hash
end)

(* -------------------------------------------------------------------- *)
let mcore_top_ntr_compare (mt1 : mpath_core_top) (mt2 : mpath_core_top) =
  match mt1, mt2 with
  | `Local    _  , `Concrete _   -> -1
  | `Concrete _  , `Local    _   -> +1
  | `Local    id1, `Local    id2 -> id_ntr_compare id1 id2
  | `Concrete p1 , `Concrete p2  -> p_ntr_compare p1 p2

let rec mcore_ntr_compare (mc1 : mpath_core) (mc2 : mpath_core) =
  match mc1.c_cnt, mc2.c_cnt with
  | Top t1, Top t2 -> mcore_top_ntr_compare t1 t2
  | Top  _, App _ -> -1
  | App  _, Top _ -> +1
  | App (c1,args1), App (c2,args2) ->
    match mcore_ntr_compare c1 c2 with
    | 0 -> List.compare m_ntr_compare args1 args2
    | n -> n

and m_ntr_compare (m1 : mpath) (m2 : mpath) =
  match mcore_ntr_compare m1.core m2.core with
  | 0 -> ocompare p_ntr_compare m1.sub m2.sub
  | n -> n

(* -------------------------------------------------------------------- *)
module MCm = MCPath.M
module HCm = MCPath.H

module Mm = MPath.M
module Hm = MPath.H

module Sm = struct
  include MPath.S

  let ntr_elements s =
    List.ksort ~key:identity ~cmp:m_ntr_compare (elements s)
end

(* -------------------------------------------------------------------- *)
(** {3 Module core path smart constructors} *)

let mcore (c_cnt : mpath_core_node) : mpath_core =
    Hsmpath_core.hashcons { c_cnt; c_tag = -1; }

let mcore_abs (id : EcIdent.t) : mpath_core =
  mcore (Top (`Local id))

let mcore_crt (p : path) : mpath_core =
  mcore (Top (`Concrete p))

let mcore_apply (c : mpath_core) (args : mpath list) : mpath_core =
  if args = [] then c  (* invariant: no empty application *)
  else
    let cnt = (* invariant: maximally grouped application *)
      match c.c_cnt with
      | App (c',args') -> App (c', args' @ args)
      | Top _ -> App (c, args)
    in
    mcore cnt

(* -------------------------------------------------------------------- *)
(** {3 Module path smart constructors} *)

let mk_mpath core sub = Hsmpath.hashcons { core; sub; m_tag = -1; }

let mpath (p : mpath_top_r) (args : mpath list) : mpath =
  match p with
  | `Local id ->
    let core = mcore_apply (mcore_abs id) args in
    mk_mpath core None

  | `Concrete (p, sub) ->
    let core = mcore_apply (mcore_crt p) args in
    mk_mpath core sub

let mpath_abs id args = mpath (`Local id) args
let mident id = mpath_abs id []

let mpath_crt p args sub = mpath (`Concrete(p,sub)) args

let mqname (mp : mpath) (x : symbol) : mpath =
  match mp.sub with
  | None     -> mk_mpath mp.core (Some (psymbol x   ))
  | Some sub -> mk_mpath mp.core (Some (pqname sub x))

(* strips arguments of a [mpath_core] *)
let rec mcore_astrip (c : mpath_core) : mpath_core =
  match c.c_cnt with
  | Top _ -> c
  | App (c, args) -> mcore_astrip c

let mastrip (mp : mpath) = mk_mpath (mcore_astrip mp.core) mp.sub

let m_apply (mp : mpath) (args : mpath list) =
  mk_mpath (mcore_apply mp.core args) mp.sub

let m_functor (mp : mpath) = mk_mpath (mcore_astrip mp.core) None

let wrap (a : ident) (k : wrap_k) (m : mpath) : mpath =
  mk_mpath (mcore (Wrap (a, k, m.core))) m.sub

(* -------------------------------------------------------------------- *)
(** {3 Module resolution} *)

(** [resolves_core ragks core args] resolves the module [$(agks( core(args) )]
    where [agks = List.rev ragks] *)
let rec resolve_core
    (agks : (ident * wrap_k) list) (core : mpath_core) (args : mpath list)
  : (ident * wrap_k) list * mpath_core_top * mpath list
  =
  match core.c_cnt with
  | Top top           -> (agks, top, args)
  | App (core, args') -> resolve_core agks core (args' @ args)
  | Wrap (ag', `Ext, mc) ->
    (** [$agks      ( ( $ag'(mc)                  ) (args) ) ->
         $agks      ( ( $ag'(mc ($cb_ag'(args)) ) )        ) ->
         ${agks,ag'}( mc ($cb_ag'(args))                   )   ] *)
    let args = List.map (wrap ag' `Cb) args in
    resolve_core ((ag', `Ext) :: agks) mc args

  | Wrap (ag', `Cb, mc) ->      (* nothing to do with arguments here *)
    resolve_core ((ag', `Cb) :: agks) mc args


(* -------------------------------------------------------------------- *)
let mtop_equal (mt1 : mpath_top_r) (mt2 : mpath_top_r) =
  match mt1, mt2 with
  | `Local id1, `Local id2 -> EcIdent.id_equal id1 id2
  | `Concrete(p1, o1), `Concrete(p2, o2) ->
    p_equal p1 p2 && oall2 p_equal o1 o2
  | _, _ -> false

(* -------------------------------------------------------------------- *)
let resolve { core; sub; } : (ident * wrap_k) list * mpath_top_r * mpath list =
  let agks, top, args = resolve_core [] core [] in
  match top, sub with
  | `Local   _ , Some _   -> assert false (* abstract modules have no sub-modules *)
  | `Local top , None     -> agks, `Local top, args
  | `Concrete p, Some sub -> agks, `Concrete (p, Some sub), args
  | `Concrete p, None     -> agks, `Concrete (p,     None), args

(* -------------------------------------------------------------------- *)
(* TODO: cost: hashconsing *)
let margs (m : mpath) : mpath list            = let _, _, x = resolve m in x
let mtop  (m : mpath) : mpath_top_r           = let _, x, _ = resolve m in x
let magks (m : mpath) : (ident * wrap_k) list = let x, _, _ = resolve m in x

(* -------------------------------------------------------------------- *)
(** {3 Module path utilities} *)

let rec mcore_is_local (mc : mpath_core) : bool =
  match mc.c_cnt with
  | Top  (`Local    _) -> true
  | Top  (`Concrete _) -> false
  | App  (c,_)         -> mcore_is_local c
  | Wrap (_,_,c)       -> mcore_is_local c

let m_is_local (mp : mpath) : bool = mcore_is_local mp.core

(* -------------------------------------------------------------------- *)
let rec mcore_is_concrete (mc : mpath_core) : bool =
  match mc.c_cnt with
  | Top  (`Local    _) -> false
  | Top  (`Concrete _) -> true
  | App  (c,_)         -> mcore_is_concrete c
  | Wrap (_,_,c)       -> mcore_is_concrete c

let m_is_concrete (mp : mpath) : bool =
  mcore_is_concrete mp.core

(* -------------------------------------------------------------------- *)
let rec mcore_get_ident (mc : mpath_core) : ident =
  match mc.c_cnt with
  | Top  (`Local    id) -> id
  | Top  (`Concrete _ ) -> assert false
  | App  (c,_)          -> mcore_get_ident c
  | Wrap (_,_,c)        -> mcore_get_ident c

let mget_ident mp = mcore_get_ident mp.core

(* -------------------------------------------------------------------- *)
let rec mcore_fv fv mc =
  match mc.c_cnt with
  | Top (`Local   id) -> EcIdent.fv_add id fv
  | Top (`Concrete _) -> fv
  | App (mc,args) ->
    List.fold_left m_fv (mcore_fv fv mc) args
  | Wrap (a, _, mc) ->
    mcore_fv (EcIdent.fv_add a fv) mc

and m_fv fv mp = mcore_fv fv mp.core

(* -------------------------------------------------------------------- *)
let rec pp_mcore fmt (mc : mpath_core) =
  let pp_args fmt args =
    assert (args <> []);
    Format.fprintf fmt "@[(%a)@]" (pp_list "," pp_m) args
  in
  match mc.c_cnt with
  | Top  (`Local    id) -> Format.fprintf fmt "%s" (EcIdent.tostring id)
  | Top  (`Concrete p ) -> Format.fprintf fmt "%s" (tostring p)
  | App  (c,args )      -> Format.fprintf fmt "%a%a" pp_mcore c pp_args args
  | Wrap (a, `Ext, c)   -> Format.fprintf fmt "$%a(%a)" EcIdent.pp_ident a pp_mcore c
  | Wrap (a, `Cb , c)   -> Format.fprintf fmt "$cb_%a(%a)" EcIdent.pp_ident a pp_mcore c

and pp_m fmt mp =
  let pp_sub fmt =
    match mp.sub with
    | None -> ()
    | Some sub -> Format.fprintf fmt ".%s" (tostring sub)
  in
  Format.fprintf fmt "%a%t" pp_mcore mp.core pp_sub

(* -------------------------------------------------------------------- *)
(** {2 Variable and procedure path} *)

type xpath = {
  x_top : mpath;
  x_sub : symbol;
  x_tag : int;
}

let x_equal   = ((==) : xpath -> xpath -> bool)
let x_hash    = fun p -> p.x_tag
let x_compare = fun p1 p2 -> x_hash p1 - x_hash p2

let x_compare_na x1 x2 =
  x_compare x1 x2 (* FIXME: doc says something about x_top being normalized *)

(* -------------------------------------------------------------------- *)
module Hsxpath = Why3.Hashcons.Make (struct
  type t = xpath

  let equal m1 m2 =
    m_equal m1.x_top m2.x_top && EcSymbols.sym_equal m1.x_sub m2.x_sub

  let hash m =
    Why3.Hashcons.combine (m_hash m.x_top) (Hashtbl.hash m.x_sub)

  let tag n p = { p with x_tag = n }
end)

(* -------------------------------------------------------------------- *)
module XPath = MakeMSH (struct
  type t  = xpath
  let tag = x_hash
end)

(* -------------------------------------------------------------------- *)
let x_ntr_compare (xp1 : xpath) (xp2 : xpath) =
  match m_ntr_compare xp1.x_top xp2.x_top with
  | 0 -> String.compare xp1.x_sub xp2.x_sub
  | n -> n

(* -------------------------------------------------------------------- *)
let xpath top sub =
  Hsxpath.hashcons { x_top = top; x_sub = sub; x_tag = -1; }

let x_fv fv xp = m_fv fv xp.x_top

let xastrip x = { x with x_top = mastrip x.x_top }
let xbasename xp = xp.x_sub

let pp_x fmt x = Format.fprintf fmt "%a.%s" pp_m x.x_top x.x_sub

(* -------------------------------------------------------------------- *)
module Mx = XPath.M
module Hx = XPath.H

module Sx = struct
  include XPath.S

  let ntr_elements s =
    List.ksort ~key:identity ~cmp:x_ntr_compare (elements s)
end

(* -------------------------------------------------------------------- *)
let rec m_tostring (m : mpath) = Format.asprintf "%a" pp_m m

let x_tostring x =
  Printf.sprintf "%s./%s"
    (m_tostring x.x_top) x.x_sub

(* -------------------------------------------------------------------- *)
module Smart : sig
  type a_psymbol   = symbol
  type a_pqname    = path * symbol
  type a_mpath_abs = ident * mpath list
  type a_mpath_crt = path * mpath list * path option
  type a_xpath     = mpath * symbol

  val psymbol   : (path * a_psymbol   ) -> a_psymbol   -> path
  val pqname    : (path * a_pqname    ) -> a_pqname    -> path
  val mpath_abs : (mpath * a_mpath_abs) -> a_mpath_abs -> mpath
  val mpath_crt : (mpath * a_mpath_crt) -> a_mpath_crt -> mpath
  val xpath     : xpath                 -> a_xpath     -> xpath
end = struct
  type a_psymbol   = symbol
  type a_pqname    = path * symbol
  type a_mpath_abs = ident * mpath list
  type a_mpath_crt = path * mpath list * path option
  type a_xpath     = mpath * symbol

  let psymbol (p, x) x' =
    if x == x' then p else psymbol x'

  let pqname (p, (q, x)) (q', x') =
    if x == x' && q == q' then p else pqname q' x'

  let mk_mpath core sub = assert false

  let mpath_abs (mp, (id, args)) (id', args') =
    if id == id' && args == args' then mp else mpath_abs id' args'

  let mpath_crt (mp, (p, args, sp)) (p', args', sp') =
    if p == p' && args == args' && sp == sp' then
      mp
    else
      mpath_crt p' args' sp'

  let xpath xp (mp', x') =
    if xp.x_top == mp' && xp.x_sub == x' then xp else xpath mp' x'
end

(* -------------------------------------------------------------------- *)
type smsubst = {
  sms_crt : path Mp.t;
  sms_id  : mpath Mid.t;
  sms_ag  : ident Mid.t;
}

(* -------------------------------------------------------------------- *)
let sms_identity : smsubst =
  { sms_crt = Mp.empty; sms_id = Mid.empty; sms_ag = Mid.empty; }

(* -------------------------------------------------------------------- *)
let sms_is_identity (s : smsubst) =
  Mp.is_empty s.sms_crt && Mid.is_empty s.sms_id && Mid.is_empty s.sms_ag

(* -------------------------------------------------------------------- *)
let sms_bind_abs (x : ident) (mp : mpath) (s : smsubst) =
  { s with sms_id = Mid.add x mp s.sms_id }

(* -------------------------------------------------------------------- *)
let sms_bind_agent (x : ident) (y : ident) (s : smsubst) =
  { s with sms_ag = Mid.add x y s.sms_ag }

(* -------------------------------------------------------------------- *)
let p_subst (s : path Mp.t) =
  if Mp.is_empty s then identity else

  let doit (aux : path -> path) (p : path) =
    match p.p_node with
    | Psymbol _ -> p
    | Pqname(q, x) -> Smart.pqname (p, (q, x)) (aux q, x) in

  let p_subst (aux : path -> path) (p : path) =
    ofdfl (fun () -> doit aux p) (Mp.find_opt p s)

  in Hp.memo_rec 107 p_subst

(* -------------------------------------------------------------------- *)
let m_subst (s : smsubst) =
  let hc = HCm.create 127 in
  let h  =  Hm.create 127 in

  (* [doit_r] with memoisation *)
  let rec doit (mp : mpath) : mpath =
    try Hm.find h mp with
    | Not_found -> let r = doit_r mp in Hm.add h mp r; r

  (* [doit_core_r] with memoisation *)
  and doit_core (mc : mpath_core) : mpath =
    try HCm.find hc mc with
    | Not_found -> let r = doit_core_r mc in HCm.add hc mc r; r

  and doit_r (mp : mpath) : mpath =
    let m = doit_core mp.core in
    let sub = mp.sub |> omap (p_subst s.sms_crt) in
    match m.sub, sub with
    | Some m_sub, None   -> m
    | None      , _      -> mk_mpath m.core sub
    | Some _    , Some _ -> assert false
  (* impossible (abstract modules have no sub-modules) *)

  and doit_core_r (mc : mpath_core) : mpath =
    match mc.c_cnt with
    | Top (`Concrete p) ->
        let p' = p_subst s.sms_crt p in
        if p_equal p p' then mk_mpath mc None else mk_mpath (mcore_crt p') None

    | Top (`Local id) ->
      begin
        try Mid.find id s.sms_id with
        | Not_found -> mk_mpath mc None
      end

    | App (c,args) ->
      let m = doit_core c in
      let args = List.Smart.map doit args in
      begin
        match m.sub with
        | Some _ -> assert (args <> []); assert false
        (* impossible (abstract modules have no sub-modules) *)

        | None -> mk_mpath (mcore_apply m.core args) None
      end

    | Wrap (a,k,c) ->
      let a = Mid.find_def a a s.sms_ag in
      wrap a k (doit_core c)
  in
  doit

let m_subst (s : smsubst) =
  if sms_is_identity s then identity else m_subst s

(* -------------------------------------------------------------------- *)
let x_subst (s : smsubst) (xp : xpath) =
  Smart.xpath xp (m_subst s xp.x_top, xp.x_sub)

let x_subst (s : smsubst) =
  if sms_is_identity s then identity else x_subst s
