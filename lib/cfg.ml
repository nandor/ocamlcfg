[@@@ocaml.warning "+a-30-40-41-42"]

let verbose = ref false

include Cfg_intf.S

type basic_block =
  { start : Label.t;
    mutable body : basic instruction list;
    mutable terminator : terminator instruction;
    mutable predecessors : Label.Set.t;
    trap_depth : int;
    mutable exns : Label.Set.t;
    mutable can_raise : bool;
    mutable can_raise_interproc : bool;
    mutable is_trap_handler : bool;
    mutable dead : bool
  }

type t =
  { blocks : basic_block Label.Tbl.t;
    fun_name : string;
    entry_label : Label.t;
    mutable fun_tailrec_entry_point_label : Label.t
  }

let create ~fun_name ~fun_tailrec_entry_point_label =
  { fun_name;
    entry_label = 1;
    blocks = Label.Tbl.create 31;
    fun_tailrec_entry_point_label
  }

let mem_block t label = Label.Tbl.mem t.blocks label

let successor_labels_normal t ti =
  match ti.desc with
  | Tailcall (Self _) -> Label.Set.singleton t.fun_tailrec_entry_point_label
  | Call { successor; _ } -> Label.Set.singleton successor
  | Switch labels -> Array.to_seq labels |> Label.Set.of_seq
  | Return | Raise _ | Tailcall (Func _) -> Label.Set.empty
  | Never -> Label.Set.empty
  | Always l -> Label.Set.singleton l
  | Parity_test { ifso; ifnot } | Truth_test { ifso; ifnot } ->
      Label.Set.singleton ifso |> Label.Set.add ifnot
  | Float_test { lt; gt; eq; uo } ->
      Label.Set.singleton lt |> Label.Set.add gt |> Label.Set.add eq
      |> Label.Set.add uo
  | Int_test { lt; gt; eq; imm = _; is_signed = _ } ->
      Label.Set.singleton lt |> Label.Set.add gt |> Label.Set.add eq

let successor_labels t ~normal ~exn block =
  match (normal, exn) with
  | false, false -> Label.Set.empty
  | true, false -> successor_labels_normal t block.terminator
  | false, true -> block.exns
  | true, true ->
      Label.Set.union block.exns (successor_labels_normal t block.terminator)

let predecessor_labels block = Label.Set.elements block.predecessors

let replace_successor_labels t ~normal ~exn block ~f =
  (* Check that the new labels are in [t] *)
  let f src =
    let dst = f src in
    if not (mem_block t dst) then
      Misc.fatal_errorf
        "Cfg.replace_successor_labels: \n\
         new successor %d not found in the cfg" dst;
    dst
  in
  if exn then block.exns <- Label.Set.map f block.exns;
  if normal then
    let desc =
      match block.terminator.desc with
      | Never -> Never
      | Always l -> Always (f l)
      | Parity_test { ifso; ifnot } ->
          Parity_test { ifso = f ifso; ifnot = f ifnot }
      | Truth_test { ifso; ifnot } ->
          Truth_test { ifso = f ifso; ifnot = f ifnot }
      | Int_test { lt; eq; gt; is_signed; imm } ->
          Int_test { lt = f lt; eq = f eq; gt = f gt; is_signed; imm }
      | Float_test { lt; eq; gt; uo } ->
          Float_test { lt = f lt; eq = f eq; gt = f gt; uo = f uo }
      | Switch labels -> Switch (Array.map f labels)
      | Tailcall (Self _) ->
          (* CR-someday gyorsh: If there is no [Tailcall Self] then we won't
             affect [t.fun_tailrec_entry_point_label]. Maybe this case should
             do nothing and [fun_tailrec_entry_point_label] should
             unilaterally be updated earlier in this function? *)
          (* CR-someday gyorsh: Move replace_successor_labels back to
             disconnect_block.ml ?

             Changing t.fun_tailrec_entry_point_label has effect on other
             blocks, it's not local to the [block] that is passed as argument
             to [replace_successor_labels].

             Suppose that there are two "Tailcall Self" sites in the
             function, say blocks L1 and L2 both have Tailcall Self as their
             terminator. Then, if we call replace_successor_labels on L1 but
             not on L2 we get an inconsistent CFG, as there is only one
             tailrec entry point.

             How do we guarantee that all other blocks that refer to
             t.fun_tailrec_entry_point_label are updated?

             [replace_successor_labels] is only used in eliminate
             fallthrough, where it is called on all predecessors of a block
             that is a fallthrough block. If a predecessor block terminates
             with tailcall self, then its successor is the block at
             t.fun_tailrec_entry_point_label and the tailrec entry point
             block has as its predecessors *all* the "tailcall self" blocks. *)
          t.fun_tailrec_entry_point_label <-
            f t.fun_tailrec_entry_point_label;
          block.terminator.desc
      | Call { call_operation; successor } ->
        Call { call_operation; successor = f successor }
      | Return | Raise _ | Tailcall (Func _) -> block.terminator.desc
    in
    block.terminator <- { block.terminator with desc }

let remove_block_exn t label =
  match Label.Tbl.find t.blocks label with
  | exception Not_found ->
      Misc.fatal_errorf "Cfg.remove_block_exn: block %d not found" label
  | _ -> Label.Tbl.remove t.blocks label

let get_block t label = Label.Tbl.find_opt t.blocks label

let get_block_exn t label =
  match Label.Tbl.find t.blocks label with
  | exception Not_found ->
      Misc.fatal_errorf "Cfg.get_block_exn: block %d not found" label
  | block -> block

let fun_name t = t.fun_name

let is_exit block =
  match block.terminator.desc with
  | Never
  | Return
  | Tailcall (Func _) ->
    true
  | Tailcall (Self _)
  | Always _
  | Parity_test _
  | Truth_test _
  | Float_test _
  | Int_test _
  | Switch _ ->
    false
  | Call _
  | Raise _ ->
    block.can_raise_interproc

let entry_label t = t.entry_label

let exit_labels t =
  Label.Tbl.to_list t.blocks
  |> List.filter (fun (_, block) -> is_exit block)
  |> List.map fst
  |> Label.Set.of_list

let fun_tailrec_entry_point_label t = t.fun_tailrec_entry_point_label

let set_fun_tailrec_entry_point_label t label =
  if not (mem_block t label) then
    Misc.fatal_errorf
      "Cfg.set_fun_tailrec_entry_point_label: \n\
       label %d not found in the cfg" label;
  t.fun_tailrec_entry_point_label <- label

let iter_blocks t ~f = Label.Tbl.iter f t.blocks

let blocks t = List.map snd (Label.Tbl.to_list t.blocks)

(* Printing for debug *)

(* The next 2 functions are copied almost as is from asmcomp/printmach.ml
   because there is no interface to call them. Eventually this won't be
   needed when we change cfg to have its own types rather than referring back
   to mach and cmm. *)
(* CR-someday gyorsh: implement desc printing, and args/res/dbg, etc,
   properly, with regs, use the dreaded Format. *)

let intcomp (comp : Mach.integer_comparison) =
  match comp with
  | Isigned c -> Printf.sprintf " %ss " (Printcmm.integer_comparison c)
  | Iunsigned c -> Printf.sprintf " %su " (Printcmm.integer_comparison c)

let intop (op : Mach.integer_operation) =
  match op with
  | Iadd -> " + "
  | Isub -> " - "
  | Imul -> " * "
  | Imulh -> " *h "
  | Idiv -> " div "
  | Imod -> " mod "
  | Iand -> " & "
  | Ior -> " | "
  | Ixor -> " ^ "
  | Ilsl -> " << "
  | Ilsr -> " >>u "
  | Iasr -> " >>s "
  | Icomp cmp -> intcomp cmp
  | Icheckbound _ -> assert false

let print_op oc = function
  | Move -> Printf.fprintf oc "mov"
  | Spill -> Printf.fprintf oc "spill"
  | Reload -> Printf.fprintf oc "reload"
  | Const_int n -> Printf.fprintf oc "const_int %nd" n
  | Const_float f -> Printf.fprintf oc "const_float %Ld" f
  | Const_symbol s -> Printf.fprintf oc "const_symbol %s" s
  | Stackoffset n -> Printf.fprintf oc "stackoffset %d" n
  | Load _ -> Printf.fprintf oc "load"
  | Store _ -> Printf.fprintf oc "store"
  | Intop op -> Printf.fprintf oc "intop %s" (intop op)
  | Intop_imm (op, n) -> Printf.fprintf oc "intop %s %d" (intop op) n
  | Negf -> Printf.fprintf oc "negf"
  | Absf -> Printf.fprintf oc "absf"
  | Addf -> Printf.fprintf oc "addf"
  | Subf -> Printf.fprintf oc "subf"
  | Mulf -> Printf.fprintf oc "mulf"
  | Divf -> Printf.fprintf oc "divf"
  | Floatofint -> Printf.fprintf oc "floattoint"
  | Intoffloat -> Printf.fprintf oc "intoffloat"
  | Specific _ -> Printf.fprintf oc "specific"
  | Probe { name; handler_code_sym } ->
      Printf.fprintf oc "probe %s %s" name handler_code_sym
  | Probe_is_enabled { name } -> Printf.fprintf oc "probe_is_enabled %s" name
  | Name_for_debugger _ -> Printf.fprintf oc "name_for_debugger"

let print_call oc = function
  | P prim_call -> (
      match prim_call with
      | External { func_symbol : string; _ } ->
          Printf.fprintf oc "external %s" func_symbol
      | Alloc { bytes : int; _ } -> Printf.fprintf oc "alloc %d" bytes
      | Checkbound _ -> Printf.fprintf oc "checkbound" )
  | F func_call -> (
      match func_call with
      | Indirect _ -> Printf.fprintf oc "indirect"
      | Direct { func_symbol : string; _ } ->
          Printf.fprintf oc "direct %s" func_symbol )

let print_reg oc r =
  let name = if Reg.anonymous r then "" else Reg.name r in
  let ty =
    match r.Reg.typ with
    | Val -> "V"
    | Addr -> "A"
    | Int -> "I"
    | Float -> "F"
  in
  Printf.fprintf oc "(%s:%s/%d " name ty r.stamp;
  match r.loc with
  | Unknown -> ()
  | Reg r -> Printf.fprintf oc "[%s])" (Proc.register_name r)
  | Stack(Local s) -> Printf.fprintf oc "[s%i])" s
  | Stack(Incoming s) -> Printf.fprintf oc "[si%i])" s
  | Stack(Outgoing s) -> Printf.fprintf oc "[so%i])" s

let print_basic oc i =
  Printf.fprintf oc "%d: " i.id;
  (match i.desc with
  | Op op -> print_op oc op
  | Reloadretaddr -> Printf.fprintf oc "Reloadretaddr"
  | Pushtrap { lbl_handler } ->
      Printf.fprintf oc "Pushtrap handler=%d" lbl_handler
  | Poptrap -> Printf.fprintf oc "Poptrap"
  | Prologue -> Printf.fprintf oc "Prologue");
  Array.iter (Printf.fprintf oc " %a" print_reg) i.arg;
  Printf.fprintf oc " ->";
  Array.iter (Printf.fprintf oc " %a" print_reg) i.res

let print_terminator oc ?(sep = "\n") ti =
  Printf.fprintf oc "%d:" ti.id;
  Array.iter (Printf.fprintf oc " %a" print_reg) ti.arg;
  Printf.fprintf oc " ->";
  Array.iter (Printf.fprintf oc " %a" print_reg) ti.res;
  Printf.fprintf oc "%s" sep;
  match ti.desc with
  | Never -> Printf.fprintf oc "deadend%s" sep
  | Always l -> Printf.fprintf oc "goto %d%s" l sep
  | Parity_test { ifso; ifnot } ->
      Printf.fprintf oc "if even goto %d%sif odd goto %d%s" ifso sep ifnot
        sep
  | Truth_test { ifso; ifnot } ->
      Printf.fprintf oc "if true goto %d%sif false goto %d%s" ifso sep ifnot
        sep
  | Float_test { lt; eq; gt; uo } ->
      Printf.fprintf oc "if < goto %d%s" lt sep;
      Printf.fprintf oc "if = goto %d%s" eq sep;
      Printf.fprintf oc "if > goto %d%s" gt sep;
      Printf.fprintf oc "if uo goto %d%s" uo sep
  | Int_test { lt; eq; gt; is_signed; imm } ->
      let cmp =
        Printf.sprintf " %s%s"
          (if is_signed then "s" else "u")
          ( match imm with
          | None -> ""
          | Some i -> " " ^ Int.to_string i )
      in
      Printf.fprintf oc "if <%s goto %d%s" cmp lt sep;
      Printf.fprintf oc "if =%s goto %d%s" cmp eq sep;
      Printf.fprintf oc "if >%s goto %d%s" cmp gt sep
  | Switch labels ->
      Printf.fprintf oc "switch%s" sep;
      for i = 0 to Array.length labels - 1 do
        Printf.fprintf oc "case %d: goto %d%s" i labels.(i) sep
      done
  | Return -> Printf.fprintf oc "Return%s" sep
  | Raise _ -> Printf.fprintf oc "Raise%s" sep
  | Call { call_operation; successor } ->
      Printf.fprintf oc "Call ";
      print_call oc call_operation;
      Printf.fprintf oc " goto %d%s" successor sep
  | Tailcall (Self _) -> Printf.fprintf oc "Tailcall self%s" sep
  | Tailcall (Func _) -> Printf.fprintf oc "Tailcall%s" sep


(*
 * This duplicates logic for Proc for the amd64 backend.
 * Proc.mli could expose some of the register sets (all_phys_regs,
 * destroyed_at_c_call) and offer a separate method for clobbers
 * of primitive operations common between Mach and Linear.
 *)

let rax = 0
let rdx = 4
let r10 = 10
let r11 = 11
let r13 = 9
let rbp = 12
let rxmm15 = 115

let all_phys_regs =
    [| 0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12
     ; 100; 101; 102; 103; 104; 105; 106; 107
     ; 108; 109; 110; 111; 112; 113; 114; 115 |]

let destroyed_at_c_call =
  if Arch.win64 then
    [| 0; 4; 5; 6; 7; 10; 11
     ; 100; 101; 102; 103; 104; 105 |]
  else
    [| 0; 2; 3; 4; 5; 6; 7; 10; 11
     ; 100; 101; 102; 103; 104; 105; 106; 107
     ; 108; 109; 110; 111; 112; 113; 114; 115 |]

let destroyed_by_plt_stub =
  if X86_proc.use_plt then [| r10; r11 |] else [| |]

let destroyed_at_alloc =
  let regs =
    if Config.spacetime then [| rax; r13 |] else [| rax |]
  in
  Array.concat [regs; destroyed_by_plt_stub]

[@@@ocaml.warning "+a-30-40-41-42-4"]
let destroyed_at_basic = function
  | Op (Intop (Idiv | Imod))
  | Op (Intop_imm((Idiv | Imod), _)) ->
    [| rax; rdx |]
  | Op (Store(Single, _, _)) ->
    [| rxmm15 |]
  | Op (Intop(Imulh | Icomp _) | Intop_imm((Icomp _), _)) ->
    [| rax |]
  | Op _ ->
    if Config.with_frame_pointers then [| rbp |] else [||]
  | Pushtrap _
  | Poptrap ->
    [| r11 |]
  | Reloadretaddr
  | Prologue ->
    [| |]

let destroyed_at_terminator = function
  | Switch _ ->
    [| rax; rdx |]
  | Raise _ ->
    all_phys_regs
  | Call { call_operation = F (Indirect _); _ }
  | Call { call_operation = F (Direct _); _ }
  | Call { call_operation = P (External { alloc = true; _ }); _ } ->
    all_phys_regs
  | Call { call_operation = P (External { alloc = false; _ }); _ } ->
    destroyed_at_c_call
  | Call { call_operation = P (Alloc _); _ } ->
    destroyed_at_alloc
  | Call { call_operation = P (Checkbound _); _ } ->
    if Config.spacetime then [| r13 |] else [| |]
  | Never
  | Always _
  | Return
  | Tailcall _
  | Parity_test _
  | Truth_test _
  | Float_test _
  | Int_test _ ->
    if Config.with_frame_pointers then [| rbp |] else [||]

let print t oc msg =
  Printf.fprintf oc "cfg for %s\n" msg;
  Printf.fprintf oc "%s\n" t.fun_name;
  Printf.fprintf oc "blocks.length=%d\n" (Label.Tbl.length t.blocks);
  let print_block label block =
    Printf.fprintf oc "\n\n\n%d:\n" label;
    List.iter (fun inst -> Printf.fprintf oc "  %a\n" print_basic inst) block.body;
    Printf.fprintf oc "  ";
    print_terminator oc block.terminator;
    Printf.fprintf oc "\npredecessors:";
    Label.Set.iter (Printf.fprintf oc " %d") block.predecessors;
    Printf.fprintf oc "\nsuccessors:";
    Label.Set.iter (Printf.fprintf oc " %d")
      (successor_labels ~normal:true ~exn:false t block);
    Printf.fprintf oc "\nexn-successors:";
    Label.Set.iter (Printf.fprintf oc " %d")
      (successor_labels ~normal:false ~exn:true t block)
  in
  Label.Tbl.iter print_block t.blocks;
  Printf.fprintf oc "\n"
