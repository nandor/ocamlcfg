(**************************************************************************)
(*                                                                        *)
(*                                 OCamlFDO                               *)
(*                                                                        *)
(*                     Greta Yorsh, Jane Street Europe                    *)
(*                                                                        *)
(*   Copyright 2019 Jane Street Group LLC                                 *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

[@@@ocaml.warning "+a-4-30-40-41-42"]

type t =
  { cfg : Cfg.t;
    mutable layout : Label.t list;
    mutable trap_depths : int Label.Tbl.t;
    mutable trap_labels : Label.t Label.Tbl.t;
    preserve_orig_labels : bool;
    mutable new_labels : Label.Set.t
  }

let create cfg ~layout ~trap_depths ~trap_labels ~preserve_orig_labels
    ~new_labels =
  { cfg; layout; trap_depths; trap_labels; preserve_orig_labels; new_labels }

let cfg t = t.cfg

let layout t = t.layout

let trap_depths t = t.trap_depths

let trap_labels t = t.trap_labels

let preserve_orig_labels t = t.preserve_orig_labels

let new_labels t = t.new_labels

let set_layout t layout = t.layout <- layout

let filter_trap_labels t ~f =
  Label.Tbl.filter_map_inplace
    (fun _trap_handler_lbl pushtrap_lbl ->
      if f ~pushtrap_lbl then Some pushtrap_lbl else None)
    t.trap_labels

let remove_from_trap_depths t label =
  if not (Label.Tbl.mem t.trap_depths label) then
    Misc.fatal_errorf "No trap depth was registered for label %a" Label.print
      label;
  Label.Tbl.remove t.trap_depths label

let remove_from_new_labels t label =
  t.new_labels <- Label.Set.remove label t.new_labels

let is_trap_handler t label = Label.Tbl.mem t.trap_labels label

(* Printing utilities for debug *)

let print t oc msg =
  Printf.fprintf oc "cfg for %s\n" msg;
  Printf.fprintf oc "%s\n" t.cfg.fun_name;
  Printf.fprintf oc "layout.length=%d\n" (List.length t.layout);
  Printf.fprintf oc "blocks.length=%d\n" (Label.Tbl.length t.cfg.blocks);
  let print_block label =
    let block = Label.Tbl.find t.cfg.blocks label in
    Printf.fprintf oc "\n%d:\n" label;
    List.iter (Cfg.print_basic oc) block.body;
    Cfg.print_terminator oc block.terminator;
    Printf.fprintf oc "\npredecessors:";
    Label.Set.iter (Printf.fprintf oc " %d") block.predecessors;
    Printf.fprintf oc "\nsuccessors:";
    List.iter (Printf.fprintf oc " %d") (Cfg.successor_labels t.cfg block)
  in
  List.iter print_block t.layout

let print_dot t ?(show_instr = true) msg =
  let filename =
    Printf.sprintf "%s%s%s.dot"
      (X86_proc.string_of_symbol "" t.cfg.fun_name)
      (if msg = "" then "" else ".")
      msg
  in
  if !Cfg.verbose then
    Printf.printf "Writing cfg for %s to %s\n" msg filename;
  let oc = open_out filename in
  Printf.fprintf oc "strict digraph \"%s\" {\n" t.cfg.fun_name;
  let print_block_dot label (block : Cfg.basic_block) index =
    let name l = Printf.sprintf "\".L%d\"" l in
    let show_index = Option.value index ~default:(-1) in
    Printf.fprintf oc "\n%s [shape=box label=\".L%d:I%d:S%d" (name label)
      label show_index (List.length block.body);
    if show_instr then (
      (* CR-someday gyorhs: Printing instruction using Printlinear doesn't
         work because of special characters like { } that need to be escaped.
         Should use sexp to print or implement a special printer. *)
      List.iter (Cfg.print_basic oc) block.body;
      Printf.fprintf oc "\npreds:";
      Label.Set.iter (Printf.fprintf oc " %d") block.predecessors;
      Cfg.print_terminator oc block.terminator );
    Printf.fprintf oc "\"]\n";
    List.iter
      (fun l -> Printf.fprintf oc "%s->%s\n" (name label) (name l))
      (Cfg.successor_labels t.cfg block)
  in
  (* print all the blocks, even if they don't appear in the layout *)
  List.iteri
    (fun index label ->
      let block = Label.Tbl.find t.cfg.blocks label in
      print_block_dot label block (Some index))
    t.layout;
  assert (List.length t.layout <= Label.Tbl.length t.cfg.blocks);
  if List.length t.layout < Label.Tbl.length t.cfg.blocks then
    Label.Tbl.iter
      (fun label block ->
        match List.find_opt (fun lbl -> label = lbl) t.layout with
        | None -> print_block_dot label block None
        | _ -> ())
      t.cfg.blocks;
  Printf.fprintf oc "}\n";
  close_out oc