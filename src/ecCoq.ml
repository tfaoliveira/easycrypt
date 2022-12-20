open EcUtils
open EcFol
open EcEnv
open EcDecl

module P  = EcProvers
module ER = EcReduction
module BI = EcBigInt
module EI = EcInductive

module WIdent  = Why3.Ident
module WTerm   = Why3.Term
module WTy     = Why3.Ty
module WTheory = Why3.Theory
module WDecl   = Why3.Decl
module WTask   = Why3.Task

type prover_call = {
  prover : Why3.Whyconf.prover ;
  call : Why3.Call_provers.prover_call ;
  steps : int option ;
  timeout : float ;
  mutable timeover : float option ;
  mutable interrupted : bool ;
}
type verdict =
  | NoResult
  | Invalid
  | Unknown
  | Timeout
  | Stepout
  | Valid
  | Failed
  | Canceled

type result = {
  verdict : verdict ;
  cached : bool ;
  solver_time : float ;
  prover_time : float ;
  prover_steps : int ;
  prover_errpos : Lexing.position option ;
  prover_errmsg : string ;
}

let result ?(cached=false) ?(solver=0.0) ?(time=0.0) ?(steps=0) verdict =
  {
    verdict ;
    cached = cached ;
    solver_time = solver ;
    prover_time = time ;
    prover_steps = steps ;
    prover_errpos = None ;
    prover_errmsg = "" ;
  }

let no_result = result NoResult
let valid = result Valid
let invalid = result Invalid
let unknown = result Unknown
let timeout t = result ~time:t Timeout
let stepout n = result ~steps:n Stepout
let failed ?pos msg = {
  verdict = Failed ;
  cached = false ;
  solver_time = 0.0 ;
  prover_time = 0.0 ;
  prover_steps = 0 ;
  prover_errpos = pos ;
  prover_errmsg = msg ;
}
let canceled = result Canceled

let is_valid = function { verdict = Valid } -> true | _ -> false

let ping_prover_call ~config p =
  let alive = ref true in
  let status = ref None in

  while !alive do
    match Why3.Call_provers.query_call p.call with
    | NoUpdates
    | ProverStarted ->
      if p.timeout > 0.0 then
        begin
          match p.timeover with
          | None ->
            let started = Unix.time () in
            p.timeover <- Some (started +. 2.0 +. p.timeout)
          | Some timeout ->
            let time = Unix.time () in
            if time > timeout then
              begin
                p.interrupted <- true ;
                Why3.Call_provers.interrupt_call ~config p.call
              end
            else Unix.sleep 1
        end;
    | InternalFailure exn ->
      let msg = Format.asprintf "@[<hov 2>%a@]"
          Why3.Exn_printer.exn_printer exn in
      status := Some (failed msg);
      alive := false
    | ProverInterrupted ->
      status := Some (canceled);
      alive := false
    | ProverFinished pr ->
      let r =
        match pr.pr_answer with
        | Timeout -> timeout pr.pr_time
        | Valid -> result ~time:pr.pr_time ~steps:pr.pr_steps Valid
        | Invalid -> result ~time:pr.pr_time ~steps:pr.pr_steps Invalid
        | OutOfMemory -> failed "out of memory"
        | StepLimitExceeded -> result ?steps:p.steps Stepout
        | Unknown _ -> unknown
        | _ when p.interrupted -> timeout p.timeout
        | Failure s -> failed s
        | HighFailure -> failed "Unknown error"
      in
      status := Some (r);
      alive := false
  done;

  !status

let call_prover_task ~timeout ~steps ~config prover call =
  let timeout = match timeout with None -> 0.0 | Some tlimit -> tlimit in
  let pcall = {
    call ; prover ;
    interrupted = false ;
    steps ; timeout ; timeover = None ;
  }
  in
  ping_prover_call ~config pcall

let run_batch pconf driver ~config ?script ~timeout ~steplimit prover task =
  let config = Why3.Whyconf.get_main config in
  let steps = match steplimit with Some 0 -> None | _ -> steplimit in
  let limit =
    let memlimit = Why3.Whyconf.memlimit config in
    let def = Why3.Call_provers.empty_limit in
    { Why3.Call_provers.limit_time = Why3.Opt.get_def def.limit_time timeout;
      Why3.Call_provers.limit_steps = Why3.Opt.get_def def.limit_steps steps;
      Why3.Call_provers.limit_mem = memlimit;
    }
  in
  let with_steps = match steps, pconf.Why3.Whyconf.command_steps with
    | None, _ -> false
    | Some _, Some _ -> true
    | Some _, None -> false
  in
  let steps = if with_steps then steps else None in
  let command = Why3.Whyconf.get_complete_command pconf ~with_steps in
  let inplace = if script <> None then Some true else None in
  let call =
    Why3.Driver.prove_task_prepared ?old:script ?inplace
      ~command ~limit ~config driver task
  in
  call_prover_task ~config ~timeout ~steps prover call

let pp_to_file f pp =
  let cout = open_out f in
  let fout = Format.formatter_of_out_channel cout in
  try
    pp fout ;
    Format.pp_print_flush fout () ;
    close_out cout
  with err ->
    Format.pp_print_flush fout () ;
    close_out cout ;
    raise err

let make_output_dir dir =
  if Sys.file_exists dir then ()
  else Unix.mkdir dir 0o770 ;

type mode =
  | Batch (* Only check scripts *)
  | Update (* Check and update scripts *)
  | Edit  (* Edit then check scripts *)
  | Fix   (* Try to check script, then edit script on non-success *)
  | FixUpdate (* Update and fix *)

let editor_command pconf config =
  try
    let ed = Why3.Whyconf.editor_by_id config pconf.Why3.Whyconf.editor in
    String.concat " " (ed.editor_command :: ed.editor_options)
  with Not_found ->
    Why3.Whyconf.(default_editor (get_main config))

let scriptfile ~(loc:EcLocation.t) ~ext =
  let l,r = loc.loc_start in
  let sid = string_of_int l ^ string_of_int r in
  let file = loc.loc_fname in
  let path = Filename.dirname file in
  let path = path ^ "/.interactive" in
  make_output_dir path;
  let name = Filename.basename file in
  let name = Filename.remove_extension name in
  Format.sprintf "%s/%s%s%s" path name sid ext

let safe_remove f = try Unix.unlink f with Unix.Unix_error _ -> ()

let updatescript ~script driver task =
  let backup = script ^ ".bak" in
  Sys.rename script backup ;
  let old = open_in backup in
  pp_to_file script
    (fun fmt ->
       ignore @@ Why3.Driver.print_task_prepared ~old driver fmt task
    );
  close_in old ;
  let d_old = Digest.file backup in
  let d_new = Digest.file script in
  if String.equal d_new d_old then safe_remove backup

let editor ~script ~merge ~config pconf driver task =
  if merge then updatescript ~script driver task ;
  let command = editor_command pconf config in
  let config = Why3.Whyconf.get_main config in
  let call =
    Why3.Call_provers.call_editor
      ~command ~config script
  in
  call_prover_task ~config ~timeout:None ~steps:None pconf.prover call

let prepare ~coqmode ~loc driver task =
  let ext = Filename.extension (Why3.Driver.file_of_task driver "S" "T" task) in
  let force = coqmode <> Batch in
  let script = scriptfile  ~loc ~ext in
  if Sys.file_exists script then Some (script, true) else
  if force then
    begin
      pp_to_file script
        (fun fmt ->
           ignore @@ Why3.Driver.print_task_prepared driver fmt task
        );
  Some (script, false)
    end
  else None

let interactive ~notify ~coqmode ~loc pconf ~config driver prover task =
  let time = 10 in
  let timeout = if time <= 0 then None else Some (float time) in

  match prepare ~coqmode ~loc driver task with
  | None ->
    notify |> oiter (fun notify -> notify `Critical (lazy (
         Format.asprintf "Missing script(s) for prover %a." Why3.Whyconf.print_prover prover
      )));
    None
  | Some (script, merge) ->
    match coqmode with
    | Batch ->
      run_batch ~script ~timeout ~config pconf driver ~steplimit:None prover task
    | Update ->
      if merge then updatescript ~script driver task ;
      run_batch ~script ~timeout ~config pconf driver ~steplimit:None prover task
    | Edit ->
      editor ~script ~merge ~config pconf driver task |> obind (fun _ ->
      run_batch ~script ~timeout ~config pconf driver ~steplimit:None prover task)
    | Fix ->
      run_batch ~script ~timeout ~config pconf driver ~steplimit:None prover task
      |> obind (fun r ->
      if is_valid r then Some r else
        editor ~script ~merge ~config pconf driver task |> obind (fun _ ->
            run_batch ~script ~timeout ~config pconf driver ~steplimit:None prover task))
    | FixUpdate ->
      if merge then updatescript ~script driver task ;
      run_batch ~script ~timeout ~config pconf driver ~steplimit:None prover task
      |> obind (fun r ->
          if is_valid r then Some r else
            let merge = false in
            editor ~script ~merge ~config pconf driver task
            |> obind (fun _ ->
                run_batch ~script ~timeout ~config pconf driver ~steplimit:None prover task))

let is_trivial (t : Why3.Task.task) =
  let goal = Why3.Task.task_goal_fmla t in
  Why3.Term.t_equal goal Why3.Term.t_true

exception CoqNotFound

let cfg = lazy (Why3.Whyconf.init_config None)

let config () = Lazy.force cfg

let build_proof_task ~notify ~coqmode ~loc task =
  try
    let config = config () in
    let provers = Why3.Whyconf.get_provers config in
    let test p = p.Why3.Whyconf.prover_name = "Coq" in
    let provers =  Why3.Whyconf.Mprover.fold
        (fun p _ acc -> if test p then p :: acc else acc)
        provers []
    in
    let prover =
      match provers with
      | [] -> raise CoqNotFound
      | h :: _ -> h
    in

    let main_conf = Why3.Whyconf.get_main config in
    let ld = Why3.Whyconf.loadpath main_conf in
    let env = Why3.Env.create_env ld in

    let pconf = Why3.Whyconf.get_prover_config config prover in
    let drv = Why3.Driver.load_driver_for_prover (Why3.Whyconf.get_main config)
        env pconf
    in
    let task = Why3.Driver.prepare_task drv task in

    if is_trivial task then
      Some valid
    else
      interactive ~notify ~coqmode ~loc pconf ~config drv prover task
  with
  | CoqNotFound ->
    notify |> oiter (fun notify -> notify `Critical (lazy (
         Format.asprintf "Missing prover Coq."
       )));
    None
  | exn ->
    notify |> oiter (fun notify -> notify `Critical (lazy (
         Format.asprintf "[Why3 Error] %a" Why3.Exn_printer.exn_printer exn
      )));
    None

let check ~loc ?notify ?(coqmode=Fix) (hyps : LDecl.hyps) (concl : form) =
  let env,_,tenv,decl = EcSmt.init hyps concl in
  let init_select _ ax = ax.ax_visibility = `Visible in
  let toadd = EcEnv.Ax.all ~check:init_select env in
  List.iter (EcSmt.trans_axiom tenv) toadd;
  let task = WTask.add_decl (EcSmt.tenv_task tenv) decl in

  match build_proof_task ~notify ~coqmode ~loc task with
  | None -> false
  | Some r -> match r.verdict with
    | Valid -> true
    | _ -> false
