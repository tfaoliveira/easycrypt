let write_line (outc : out_channel) (line : string) (indentation : int) : unit =
  output_string outc ((String.concat "" (List.init indentation (fun _ -> "\t"))) ^ line ^ "\n")

let write_html_head (outc : out_channel) (fn: string) (kind : EcLoader.kind) : unit =
  let thk = 
    match kind with
    | `Ec -> "Theory"
    | `EcA -> "Abstract Theory"
  in
  write_line outc "<head>" 1;
  write_line outc "<title>" 2;
  write_line outc (Printf.sprintf "%s %s" thk fn) 3;
  write_line outc "</title>" 2;
  write_line outc "</head>" 1
  
let write_section_global (outc : out_channel) (fn : string) (globdoc : string list) = ()

let write_html_body (outc : out_channel) (fn : string) (scope : EcScope.scope) : unit =
  write_line outc "<body>" 1;
  (* 
  write_section_global outc fn scope.sc_locdoc;
  write_section_types outc fn 
  write 
  *)
  write_line outc "</body>" 1

(* input = input name, scope contains all documentation items *)
let generate_html (fname : string option) (scope : EcScope.scope) : unit =
  match fname with
  | Some fn ->
      let kind =
        try  EcLoader.getkind (Filename.extension fn)
        with EcLoader.BadExtension _ -> assert false 
      in

      let hn = (Filename.remove_extension fn) ^ ".html" in
      
      let outc = open_out hn in
      
      write_line outc "<html>" 0;

      write_html_head outc fn kind;
      write_html_body outc fn scope;
      
      write_line outc "</html>" 0;

      close_out outc;

  | None -> ()