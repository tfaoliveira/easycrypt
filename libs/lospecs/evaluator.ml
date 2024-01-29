open Ast

type bitword = Z.t * int

let default_int_size = 256

let full_bitmask (n:int) : Z.t = 
  Z.((one lsl n) - one)

let rec eval_aexpr (ctxt: bitword IdentMap.t) (e: aexpr) : bitword =
  let { node = e_; type_ = t_; } = e in
  match e_ with 
  | EVar v -> (match t_ with 
    | `W n -> (match IdentMap.find_opt v ctxt with
      | Some bw -> bw
      | None -> failwith ("Variable " ^ (Ident.name v) ^ " not in evaluation context"))
    | _ -> failwith "vars shouldn't be integers?") (* assuming integers have 256 bits *) 


  | EInt i -> (Z.of_int i, default_int_size) 
  (* Need to know how to handle this case, probably good enough for now *)

  | ESlice (eb, (es, len, scale)) -> (* verify indianess on this & check new syntax *)
      let bw = eval_aexpr ctxt eb in
      let sz = len*scale in
      let sa = (match es.node with
      | EInt sa -> sa
      | _       -> eval_aexpr ctxt es |> fst |> Z.to_int)
      in begin 
        assert (sa + sz <= snd bw);
        (Z.(((fst bw) asr sa) land ((one lsl (sz)) - one)), sz)
      end

  | EMap ((`W n, `W m), (params, fb), args) -> 
      let bwargs = List.map (eval_aexpr ctxt) args in
      let bwargs = begin 
        assert (List.fold_left (&&) true (List.map (fun x -> snd x == n*m) bwargs));
        List.map fst bwargs
      end in
      let subs = List.combine (List.map fst params) bwargs in
      let k = (match fb.type_ with | `W k -> k | _ -> failwith "anon fun in map should ret word") in
      let res = 0 --^ m 
        |> Enum.map (fun i -> 
          let map_ctxt = List.fold_left (fun acc x -> IdentMap.add (fst x) (Z.((snd x asr (Int.mul i n)) land (full_bitmask n)), n) acc) ctxt subs
          in let (res, n_) = eval_aexpr (map_ctxt) fb 
          in begin
            assert (n_ == n);
            assert (Z.(res < (one lsl n)));
            (Z.(res lsl (Int.mul i n)))
          end
        ) |> Enum.fold Z.(lor) Z.zero
      in (res, n*m)

  | EConcat (`W n, args) -> 
    let args = List.map (eval_aexpr ctxt) args in
    begin 
      assert (List.hd args |> snd == n);
      (List.fold_left (fun acc x -> Z.((acc lsl n) + (fst x))) (Z.of_int 0) args, n*(List.length args))
    end

  | ERepeat (`W n, (e, i)) -> 
    let bw = eval_aexpr ctxt e in
    begin
      assert (snd bw == n);
      let v = (0 --^ i |> Enum.fold (fun acc x -> 
      Z.((acc lsl (n)) + (fst bw))) (Z.of_int 0))
      in (v, n*i)
    end

  (* might need refactoring *)
  | EShift (lr, la, (eb, es)) -> 
      let (bb, sz) = eval_aexpr ctxt eb in
      let bs = eval_aexpr ctxt es |> fst |> Z.to_int in
      ((match (lr, la) with
      | (`L,  _) -> Z.(bb lsl bs)
      | (`R, `L) -> Z.(bb asr bs)
      | (`R, `A) -> Z.(bb asr bs +
                    (if bb land (one lsl (Int.sub sz 1)) <> zero
                    then (one lsl sz) - (one lsl (Int.sub sz bs))
                    else zero
                    ))
      ), sz)

  | EExtend (us, `W n, e) ->
    (match us with
    | `U -> 
      let bw = (eval_aexpr ctxt) e in
      (fst bw, n)
    | `S -> 
      let bw = (eval_aexpr ctxt) e in
      if Z.((fst bw) < (one lsl (Int.sub (snd bw) 1)))
      then ((fst bw), n)
      else (Z.((fst bw) - (one lsl (snd bw)) + (one lsl (n))), n)
    )



  | ESat (us, `W n, e) -> (* first sat approximation: sat-length bits depend on everything *)
    let bw = eval_aexpr ctxt e in
    ((match us with
     | `U -> if Z.((fst bw) < (one lsl n)) then (fst bw) else (full_bitmask (n))
     | `S -> if Z.((fst bw) < (one lsl (Int.sub n 1))) then (fst bw) 
             else (if Z.(((fst bw) - (one lsl (snd bw))) < -(one lsl (Int.sub n 1)))
             then Z.(one lsl (Int.sub n 1)) else full_bitmask (n-1))), (snd bw))

 (*
  | EApp (f, es) -> 
    (match IdentMap.find_opt f ctxt with
      | None -> failwith (String.concat " " [(Ident.name f); "function binding not found"])
      | Some (args, d) -> 
        let subs = List.combine 
                  (List.map (fun arg -> arg |> fst) args) 
                  (List.map (bd_aexpr ctxt) es) in
        List.fold_left (fun d sub -> propagate ~offset:0 (fst sub) (snd sub) d) d subs
    )

  | ELet ((v, args, e1), e2) -> (* expand this *)
      (match args with
        | None | Some [] ->
          let bd1, bd2 = ((bd_aexpr ctxt) e1, (bd_aexpr ctxt) e2) in
          propagate ~offset:0 v bd1 bd2
        | Some args -> 
          bd_aexpr (IdentMap.add v (args, ((bd_aexpr ctxt) e1)) ctxt) e2
      )
*) 

  (* using C style semantics for conditionals *)
  | ECond (ec, (ect, ecf)) ->
      let bd, bdt, bdf = ((eval_aexpr ctxt) ec, (eval_aexpr ctxt) ect, (eval_aexpr ctxt) ecf) in
      if Z.((fst bd) <> zero) then bdt else bdf


  | ENot (`W n, e) ->
      let bw = eval_aexpr ctxt e in
      begin 
        assert (snd bw == n);
        (Z.((fst bw) lxor (full_bitmask n)), snd bw)
      end


  | EIncr (`W n, e) -> (* semantics = e + 1 *)
    let bw = eval_aexpr ctxt e in
    begin
      assert (n == snd bw);
      (Z.(((fst bw) + one) land (full_bitmask n)), n)
    end

  (* ignoring overflow for now *)
  | EAdd (`W n, us, (e1, e2)) -> (* add and sub assuming no overflow *)
    let bw1 = eval_aexpr ctxt e1 in
    let bw2 = eval_aexpr ctxt e2 in
    let () = (assert (snd bw1 == snd bw2 && snd bw1 == n)) in
    let res = Z.( (fst bw1) + (fst bw2)) in
    (match us with
    | `Word ->   (Z.(res land (full_bitmask n)), n)
    | `Sat `U -> ((if Z.(res > (one lsl n)) 
                  then full_bitmask n 
                  else res), n)
    | `Sat `S -> (if Z.(res < (one lsl (Int.sub n 1))) 
                  then res
                  else (if Z.((res - (one lsl n)) < -(one lsl (Int.sub n 1)))
                        then Z.(one lsl (Int.sub n 1)) 
                        else full_bitmask (n-1)))
                  , n)
 
  | ESub (`W n, (e1, e2)) -> 
      let b1 = eval_aexpr ctxt e1 in
      let b2 = eval_aexpr ctxt e2 in
      begin
        assert (snd b1 == snd b2);
        assert (snd b1 == n);
        let res = Z.((fst b1) - (fst b2)) in
        if Z.(res < zero) then 
        (Z.(res + (one lsl n)), n)
        else (res, n)
      end

  | EOr  (`W n, (e1, e2)) -> 
    let b1 = eval_aexpr ctxt e1 in
    let b2 = eval_aexpr ctxt e2 in
    begin
      assert (snd b1 == snd b2);
      assert (snd b1 == n);
      (Z.((fst b1) lor (fst b2)), n)
    end

  | EAnd (`W n, (e1, e2)) -> 
    let b1 = eval_aexpr ctxt e1 in
    let b2 = eval_aexpr ctxt e2 in
    begin
      assert (snd b1 == snd b2);
      assert (snd b1 == n);
      (Z.((fst b1) land (fst b2)), n)
    end

(*
  | EMul (mulk, `W n, (e1, e2)) -> (* recheck n bounds for consistency *)
      let bw1 = eval_aexpr ctxt e1 in
      let bw2 = eval_aexpr ctxt e2 in
      begin
        assert (n == snd bw1);
        assert (snd b1 == snd bw2);
        (match mulk with
        | `U hld ->
        let res = Z.((fst b1) * (fst b2))
      end
*)

 
  | ECmp (`W n, us, gte, (e1, e2)) -> (* check this *)
    let bw1 = eval_aexpr ctxt e1 in
    let bw2 = eval_aexpr ctxt e2 in
    let (b1, b2) = (match us with
    | `U -> (fst bw1, fst bw2)
    | `S -> ((if Z.((fst bw1) < (one lsl (Int.sub n 1))) then (fst bw1) else Z.((fst bw1) - (one lsl n))),
             (if Z.((fst bw2) < (one lsl (Int.sub n 1))) then (fst bw2) else Z.((fst bw2) - (one lsl n)))))
    in ((match gte with
    | `Gt -> if b1 >  b2 then Z.one else Z.zero
    | `Ge -> if b1 >= b2 then Z.one else Z.zero
    ), n)

(*
  | EAssign (eb, (eo, _, sz), er) -> 
      let bd = bd_aexpr ctxt eb in
      let od = bd_aexpr ctxt eo in
      let rd = bd_aexpr ctxt er in
      let k = (match eb.type_ with | `W n -> n | _ -> failwith "Cant slice assign an int") in
      1 --^ (k/sz) |> Enum.fold (fun d i -> 
        merge (offset ~offset:(sz*i) rd) d) rd
      |> merge rd |> merge bd |> merge (chunk ~csize:k ~count:1 od) 
*)

(*
  (* propagate v deps to t deps in d *)
and propagate ~(offset:int) (v: ident) (t: deps) (d: deps) : deps =
  Map.Int.map (fun d1 -> 
    match (IdentMap.find_opt v d1) with
    | None -> d1
    | Some si -> si |> Set.Int.enum 
      |> Enum.fold (fun acc i -> merge1 acc (Option.default (IdentMap.empty) (Map.Int.find_opt (i + offset) t))) (IdentMap.remove v d1)) d
*)

let eval_adef (df: adef) (args: bitword list) =
  assert (List.compare_lengths df.arguments args == 0);
  eval_aexpr (List.combine (List.map fst df.arguments) args |> List.enum |> IdentMap.of_enum) df.body
