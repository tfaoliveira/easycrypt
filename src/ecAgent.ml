open EcUtils
open EcIdent

(* -------------------------------------------------------------------- *)
type error =
  | NotDisjoint of EcIdent.t list (* TODO: cost: unused for now *)
  (* | Unbound of EcIdent.t *)

let pp_error fmt = function
  | NotDisjoint l ->
    Format.fprintf fmt "@[<hov 2>agent names are not disjoints:@ @[%a@]@]"
      (pp_list " " EcIdent.pp_ident) l
  (* | Unbound id -> assert false *)  (* TODO: cost: runtime error or user-level error? *)

exception InstantiationFailure of error

let error e = raise (InstantiationFailure e)

(* -------------------------------------------------------------------- *)
type agent_map = EcIdent.t EcIdent.Mid.t

(* -------------------------------------------------------------------- *)
type constr = EcIdent.t list    (* agent names must be disjoint *)

type constraints = constr list

let pp_constr fmt (c : constr) =
  Format.fprintf fmt "@[<hov 2>[$ %a]@]"
    (pp_list " " EcIdent.pp_ident) c

let pp_constrs fmt (c : constraints) =
  Format.fprintf fmt "@[<hov 2>%a@]"
    (pp_list ";@ " pp_constr) c

(* -------------------------------------------------------------------- *)
let no_duplicates agents : bool =
  Sid.cardinal (Sid.of_list agents) = List.length agents

(* -------------------------------------------------------------------- *)
let empty = []

let is_empty = List.for_all ((=) [])

let closed (c : constraints) (map : agent_map) : bool =
  let check (c1 : constr) =
    let agents = List.map (fun id -> Mid.find id map) c1 in
    no_duplicates agents
  in
  List.for_all check c

let open_constraints (c : constraints) (agents :  EcIdent.t list) : agent_map * constraints =
  let m, agents =
    List.fold_left_map (fun m ag ->
        let ag' = EcIdent.fresh ag in
        (Mid.add ag ag' m, ag')
      ) Mid.empty agents
  in
  (m, agents :: c)
