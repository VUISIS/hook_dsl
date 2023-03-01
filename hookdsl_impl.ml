open Cil_types
open Logic_typing

class process_hook_def out = object
  inherit Visitor.frama_c_inplace

  method! vvdec _ =
    Format.fprintf out "vvdec\n";
    Cil.DoChildren

  method! vfile _ =
    Format.fprintf out "vfile\n";
    Cil.DoChildren

  method! vglob_aux g =
    match g with
    | GType _ -> Format.fprintf out "GType\n"; Cil.DoChildren
    | GCompTag _ -> Format.fprintf out "GCompTag\n"; Cil.DoChildren
    | GCompTagDecl _ -> Format.fprintf out "GCompTagDecl\n"; Cil.DoChildren
    | GEnumTag _ -> Format.fprintf out "GEnumTag\n"; Cil.DoChildren
    | GEnumTagDecl _ -> Format.fprintf out "GEnumTagDecl\n"; Cil.DoChildren
    | GVarDecl _ -> Format.fprintf out "GVarDecl\n"; Cil.DoChildren
    | GFunDecl(_, vi, _) ->
        Format.fprintf out "function "; Format.pp_print_string out vi.vname;
        Format.fprintf out "\n";
        Cil.DoChildren
    | GVar _ -> Format.fprintf out "GVar\n"; Cil.DoChildren
    | GFun _ -> Format.fprintf out "GFun\n"; Cil.DoChildren
    | GAsm _ -> Format.fprintf out "GAsm\n"; Cil.DoChildren
    | GPragma _ -> Format.fprintf out "GPragma\n"; Cil.DoChildren
    | GText _ -> Format.fprintf out "GText\n"; Cil.DoChildren
    | GAnnot _ -> Format.fprintf out "GAnnot\n"; Cil.DoChildren

  method! vstmt_aux _ =
    Format.fprintf out "vstmt_aux\n";
    Cil.DoChildren
end

module Self = Plugin.Register(struct
  let name = "hook DSL"
  let shortname = "hook-dsl"
  let help = "parse DSL for defining hooks"
end)

module Enabled = Self.False(struct
  let option_name = "-cfg"
  let help =
   "when on (off by default), computes the CFG of all functions."
end)
module OutputFile = Self.String(struct
  let option_name = "-cfg-output"
  let default = "cfg.dot"
  let arg_name = "output-file"
  let help = "file where the graph is output, in dot format."
end)

let is_hookable g =
  let has_hook beh =
    let is_hook ext =
      ext.ext_name = "hook" in
    (List.find_opt is_hook beh.b_extended) != None
  in
  match g with
  | GFunDecl(spec, _, _) -> (List.find_opt has_hook spec.spec_behavior) != None
  | _ -> false
  
let get_alt_hook_name ekind =
  match ekind with
  | Ext_id _ -> Printf.printf "ekind = Ext_Id\n"; None
  | Ext_terms ts -> Printf.printf "ekind = Ext_terms\n"; 
      Printf.printf "list length is %d\n" (List.length ts); 
      if (List.length ts) > 0 then
        match (List.hd ts).term_node with
        | TConst lc ->
            Printf.printf "term_node is TConst\n";
            (match lc with
             | LStr s -> Option.some s
             | Integer _ -> Printf.printf "logic_constant is Integer\n"; None
             | LWStr _ -> Printf.printf "logic_constant is LWStr\n"; None
             | LChr _ -> Printf.printf "logic_constant is LChr\n"; None
             | LReal _ -> Printf.printf "logic_constant is LReal\n"; None
             | LEnum _ -> Printf.printf "logic_constant is LEnum\n"; None)
        | _ -> None
      else
        None
  | Ext_preds _ -> Printf.printf "ekind = Ext_preds\n"; None
  | Ext_annot _ -> Printf.printf "ekind = Ext_annot\n"; None

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
    vi.vname <- get_hook_name (vi.vname ^ "_hook") spec.spec_behavior;
    Printf.printf "Hook function name set to %s\n" vi.vname;
    vi

let rename_hook fundec =
  match fundec with
  | GFunDecl(spec, vi, l) -> GFunDecl(spec, rename_func vi spec, l)
  | _ -> fundec

let handle_global out g =
    match g with
    | GType _ -> Format.fprintf out "GType\n"
    | GCompTag _ -> Format.fprintf out "GCompTag\n"
    | GCompTagDecl _ -> Format.fprintf out "GCompTagDecl\n"
    | GEnumTag _ -> Format.fprintf out "GEnumTag\n"
    | GEnumTagDecl _ -> Format.fprintf out "GEnumTagDecl\n"
    | GVarDecl _ -> Format.fprintf out "GVarDecl\n"
    | GFunDecl(spec, vi, _) ->
        let _ = rename_hook g in
        Printf.printf "There are %d behaviors in function %s\n"
          (List.length spec.spec_behavior) vi.vname;
        if List.length spec.spec_behavior > 0 then
          let ext = List.hd spec.spec_behavior in
          (Printf.printf "Spec name %s\n" ext.b_name;
           Printf.printf "extension list has %d items\n" (List.length ext.b_extended)
          );
        Format.fprintf out "function "; Format.pp_print_string out vi.vname;
        Format.fprintf out "\n";
    | GVar _ -> Format.fprintf out "GVar\n"
    | GFun _ -> Format.fprintf out "GFun\n"
    | GAsm _ -> Format.fprintf out "GAsm\n"
    | GPragma _ -> Format.fprintf out "GPragma\n"
    | GText _ -> Format.fprintf out "GText\n"
    | GAnnot _ -> Format.fprintf out "GAnnot\n"

let create_hook_decl g =
  match g with
  | GFunDecl(spec, vi, loc) -> GFunDecl(spec, vi, loc)
  | _ -> g

let run () =
  Printf.eprintf "Hookdsl starting\n";
  let chan = open_out "hook.out" in
  let fmt = Format.formatter_of_out_channel chan in
(*  Visitor.visitFramacFileSameGlobals (new process_hook_def fmt) (Ast.get ());*)
  Printer.pp_file fmt (Ast.get());
  Format.fprintf fmt "%!";
  close_out chan

let process_file file =
  let chan = open_out "hook.out" in
  let fmt = Format.formatter_of_out_channel chan in
  List.iter (handle_global fmt) (List.filter is_hookable file.globals);
  Format.fprintf fmt "%!";
  close_out chan
  
let type_hook typing_context _loc l =
  let type_term ctxt env (expr : Logic_ptree.lexpr) =
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
