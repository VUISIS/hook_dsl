open Cil_types
open Logic_typing

module Self = Plugin.Register(struct
  let name = "hook DSL"
  let shortname = "hook-dsl"
  let help = "parse DSL for defining hooks"
end)

module Enabled = Self.False(struct
  let option_name = "-hook"
  let help =
   "when on (off by default), creates a hook template"
end)

module OutputFile = Self.String(struct
  let option_name = "-hook-output"
  let default = "gen_hook.c"
  let arg_name = "output-file"
  let help = "file where hook template is written"
end)

let get_filename g =
  match g with
  | GFunDecl(_, vi, _) -> vi.vname
  | _ -> ""

let is_hookable g =
  Printf.printf "Checking to see if %s is hookable\n" (get_filename g);
  let has_hook beh =
    let is_hook ext =
      Printf.printf "Looking for hook keyword in ext %s\n" ext.ext_name;
      ext.ext_name = "hook" in
    (List.find_opt is_hook beh.b_extended) != None
  in
  match g with
  | GFunDecl(spec, _, _) ->
      let res = (List.find_opt has_hook spec.spec_behavior) != None in
      (if res then
        Printf.printf("Hookable\n")
      else
        Printf.printf("Not hookable\n"); res)
  | GFun(dec,_) ->
      let res = (List.find_opt has_hook dec.sspec.spec_behavior) != None in
      (if res then
        Printf.printf("Hookable\n")
      else
        Printf.printf("Not hookable\n"); res)

  | _ -> false
  
let get_alt_hook_name ekind =
  match ekind with
  | Ext_id _ -> None
  | Ext_terms ts -> 
      if (List.length ts) > 0 then
        match (List.hd ts).term_node with
        | TConst lc ->
            (match lc with
             | LStr s -> Option.some s
             | Integer _ -> None
             | LWStr _ -> None
             | LChr _ -> None
             | LReal _ -> None
             | LEnum _ -> None)
        | _ -> None
      else
        None
  | Ext_preds _ -> None
  | Ext_annot _ -> None

let rec find_hook_in_extended ext = 
  match ext with
  | (e::es) ->
      if e.ext_name = "hook" then
        let alt_hook_name = get_alt_hook_name e.ext_kind in
        if alt_hook_name != None then
          alt_hook_name
        else
          find_hook_in_extended es
      else
        find_hook_in_extended es
  | [] -> None

let rec find_hook_in_spec beh_list =
  match beh_list with
  | (b::bs) ->
      let hook_name = find_hook_in_extended b.b_extended in
      if hook_name != None then
        hook_name
      else
        find_hook_in_spec bs
  | [] -> None

let get_hook_name default_name beh =
  let new_name = find_hook_in_spec beh in
    Option.value new_name ~default:default_name

let rename_func vi spec =
  { vi with vstorage = Extern; vname = get_hook_name (vi.vname ^ "_hook") spec.spec_behavior }

let rename_hook fundec =
  match fundec with
  | GFunDecl(spec, vi, l) -> GFunDecl(spec, rename_func vi spec, l)
  | GFun(dec, l) ->
      let f =
        { svar=rename_func dec.svar dec.sspec; sformals = []; slocals = [];
          smaxid=0;
          sbody = { battrs = []; bscoping=true; blocals = []; bstatics = []; bstmts = []};
          smaxstmtid=None;
          sallstmts=[];
          sspec=dec.sspec 
        } in
      GFun(f, l)
  | _ -> fundec

let fun_to_decl g =
  match g with
  | GFun(dec, loc) -> GFunDecl(dec.sspec, dec.svar, loc)
  | _ -> g

let strip_fun_body g =
  match g with
  | GFun(dec, loc) ->
      Printf.printf("Generating from GFun\n");
      let f =
        { svar=dec.svar; sformals = []; slocals = [];
          smaxid=0;
          sbody = { battrs = []; bscoping=true; blocals = []; bstatics = []; bstmts = []};
          smaxstmtid=None;
          sallstmts=[];
          sspec=dec.sspec 
        } in
      GFun(f, loc)
  | _ -> g

let generate_hook_function g =
  Printf.printf("Generating hook function\n");
  match g with
  | GFunDecl(spec, vi, loc) ->
      Printf.printf("Generating from GFunDecl\n");
      let f = 
        { svar= vi; sformals = []; slocals = [];
          smaxid=0;
          sbody = { battrs = []; bscoping=true; blocals = []; bstatics = []; bstmts = []};
          smaxstmtid=None;
          sallstmts=[];
          sspec=spec 
          } in
      GFun(f, loc)
  | GFun(dec, loc) ->
      Printf.printf("Generating from GFun\n");
      let f =
        { svar=dec.svar; sformals = []; slocals = [];
          smaxid=0;
          sbody = { battrs = []; bscoping=true; blocals = []; bstatics = []; bstmts = []};
          smaxstmtid=None;
          sallstmts=[];
          sspec=dec.sspec 
        } in
      GFun(f, loc)
  | _ -> g


let write_globals filename globals =
  let chan = open_out filename in
  let fmt = Format.formatter_of_out_channel chan in
  Cil_printer.pp_file fmt { fileName = Filepath.Normalized.of_string filename;
    globals = globals; globinit = None; globinitcalled = false };
  close_out chan
  
(*
let create_hook_filename file =
  let filename = Filepath.Normalized.to_pretty_string file.fileName in
  let prefix = String.sub filename 0 ((String.length filename) - 2) in
  String.cat prefix "_hook.c"
  *)

let create_hook_filename _ =
  OutputFile.get ()

let process_file file =
  let hookable_globals = List.map strip_fun_body (List.filter is_hookable file.globals) in
  let _ = List.iter (fun g -> Printf.printf "%s is hookable\n" (get_filename g)) hookable_globals in
  write_globals (create_hook_filename file) 
    (List.append (List.map rename_hook (List.map fun_to_decl hookable_globals))
      (List.append
            (List.map fun_to_decl hookable_globals)
            (List.map generate_hook_function hookable_globals)))
  
let type_hook typing_context _loc l =
  let type_term ctxt env (expr : Logic_ptree.lexpr) =
    Printf.printf "In type hook";
    match expr.lexpr_node with
    | Logic_ptree.PLvar hook_name -> Logic_const.tstring (String.sub hook_name 1 ((String.length hook_name)-1))
    | _ -> typing_context.type_term ctxt env expr
  in
    let typing_context = { typing_context with type_term} in
    let res = List.map (typing_context.type_term typing_context (Lenv.empty ())) l
    in
    Ext_terms res

let () = Acsl_extension.register_behavior "hook" type_hook false

let category = File.register_code_transformation_category "hook_dsl"

let () = File.add_code_transformation_before_cleanup category process_file

(* let () = Db.Main.extend run *)
