(* -------------------------------------------------------------------- *)
open Lexing

(* -------------------------------------------------------------------- *)
type range = {
  rg_fname : string;
  rg_begin : int * int;
  rg_end   : int * int;  
} [@@deriving yojson]

type 'a loced = { range : range; data : 'a; } [@@deriving yojson]

(* -------------------------------------------------------------------- *)
module Lc = struct
  let of_positions (p1 : position) (p2 : position) : range =
    assert (p1.pos_fname = p2.pos_fname);

    let mk_range (p : position) =
      (p.pos_lnum, p.pos_cnum - p.pos_bol) in

    { rg_fname = p1.pos_fname; rg_begin = mk_range p1; rg_end = mk_range p2; }

  let of_lexbuf (lx : Lexing.lexbuf) : range =
    let p1 = Lexing.lexeme_start_p lx in
    let p2 = Lexing.lexeme_end_p lx in
    of_positions p1 p2

  let unloc (x : 'a loced) : 'a =
    x.data

  let map (f : 'a -> 'b) (x : 'a loced) : 'b loced =
    { x with data = f x.data }
end

(* -------------------------------------------------------------------- *)
type symbol = string [@@deriving yojson]
type word = [ `W of int ] [@@deriving yojson]
type type_ = [ `Unsigned | `Signed | word ] [@@deriving yojson]

(* -------------------------------------------------------------------- *)
type psymbol = symbol loced [@@deriving yojson]
type pword = word loced [@@deriving yojson]
type ptype = type_ loced [@@deriving yojson]
type parg = psymbol * pword [@@deriving yojson]
type pargs = parg list [@@deriving yojson]
type pfname = psymbol * pword list option [@@deriving yojson]

(* -------------------------------------------------------------------- *)
type pexpr_ =
  | PEParens of pexpr 
  | PEFName of pfname
  | PEInt of int
  | PEFun of pargs * pexpr
  | PELet of (psymbol * pargs option * pexpr) * pexpr
  | PESlice of pexpr * (pexpr * pexpr option * pexpr option)
  | PEApp of pfname * pexpr option loced list
[@@deriving yojson]

and pexpr = pexpr_ loced [@@deriving yojson]

type pdef = { name : symbol; args : pargs; rty : pword; body : pexpr }
[@@deriving yojson]

type pprogram = pdef list [@@deriving yojson]
