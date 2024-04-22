(* -------------------------------------------------------------------- *)
open EcSymbols
open EcAst

module Sid = EcIdent.Sid
module Mid = EcIdent.Mid

(* -------------------------------------------------------------------- *)
include EcCoreModules

(* -------------------------------------------------------------------- *)
module OI = PreOI

let change_oinfo restr f oi =
  { restr with mr_oinfos = Msym.add f oi restr.mr_oinfos }

let add_oinfo restr f oi = change_oinfo restr f oi

let oicalls_filter restr f filter =
  match Msym.find f restr.mr_oinfos with
  | oi -> change_oinfo restr f (OI.filter filter oi)
  | exception Not_found -> restr

let change_oicalls restr f ocalls =
  let oi = match Msym.find f restr.mr_oinfos with
    | oi -> OI.filter (fun x -> List.mem x ocalls) oi
    | exception Not_found -> OI.mk ocalls in
  add_oinfo restr f oi

(* -------------------------------------------------------------------- *)
let mty_hash  = EcCoreFol.mty_hash
let mty_equal = EcCoreFol.mty_equal

let mr_equal  = EcCoreFol.mr_equal
