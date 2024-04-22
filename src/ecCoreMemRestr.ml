open EcIdent
open EcPath
open EcAst

let mer_empty = Empty
let mer_quantum = Quantum
let mer_classical = Classical

let mer_full = Union(mer_quantum, mer_classical)

let mer_union s1 s2 =
  match s1, s2 with
  | Empty, s | s, Empty -> s
  | _, _ -> Union(s1, s2)

let mer_diff s1 s2 =
  match s1, s2 with
  | Empty, _ -> Empty
  | _, Empty -> s1
  | _, _ -> Diff(s1, s2)

let mer_inter s1 s2 =
  match s1, s2 with
  | Empty, _ | _, Empty -> Empty
  | _, _ -> Inter(s1, s2)

let mer_vars (xs : Sglob.t) =
  Sglob.fold (fun g mer -> mer_union (Var g) mer) xs mer_empty

let mer_classicals (xs : Sx.t) =
  Sx.fold (fun g mer -> mer_union (Var(`Classical, g)) mer) xs mer_empty

let mer_quantums (xs : Sx.t) =
  Sx.fold (fun g mer -> mer_union (Var(`Quantum, g)) mer) xs mer_empty


let mer_globfun ff_params ff_xp =
  let fv = x_fv Mid.empty ff_xp in
  let _, ff_params =
    List.fold_right (fun (x,mty) (fv, params) ->
        if Mid.mem x fv then
          let fv = fv_union (mty_fv mty) (Mid.remove x fv) in
          fv, (x,mty)::params
        else
          fv, params) ff_params (fv, [])
  in
  GlobFun {ff_params; ff_xp }

let mer_globfuns ff_params (xs : Sx.t) =
  Sx.fold (fun f mer -> mer_union (mer_globfun ff_params f) mer) xs mer_empty
