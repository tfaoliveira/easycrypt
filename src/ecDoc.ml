let write_html_head (outc : out_channel) (fn: string) (kind : EcLoader.kind) : unit =
  let thk = 
    match kind with
    | `Ec -> "Theory"
    | `EcA -> "Abstract Theory"
  in  
  output_string outc (Printf.sprintf "<html><head><title>%s %s</title></head>" thk fn)

let write_section_global (outc : out_channel) (fn : string) (globdoc : string list) = ()

let write_html_body (outc : out_channel) (fn : string) (scope : EcScope.scope) : unit =
  output_string outc "<body>";
  (* 
  write_section_global outc fn scope.sc_locdoc;
  write_section_types outc fn 
  write 
  *)
  output_string outc "</body>"

(* input = input name, scope contains all documentation items *)
let generate_html (fname : string option) (scope : EcScope.scope) : unit =
  match fname with
  | Some fn ->
      let kind =
        try  EcLoader.getkind (Filename.extension fn)
        with EcLoader.BadExtension _ -> assert false 
      in

      let hname = (Filename.remove_extension fn) ^ ".html" in
      
      let outc = open_out hname in
      
      write_html_head outc fn kind;
      write_html_body outc fn scope;
      
  | None -> ()