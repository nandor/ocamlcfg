open Data_flow_analysis

(** A map using the physical location of a register as key. *)
module RegMap = Map.Make(struct
  type t = Reg.t
  let compare a b = Stdlib.compare a.Reg.loc b.Reg.loc
end)

(** Same as Cmm.lub_comnent, except it picks the register with the correct type. *)
let reg_lub a b =
  let open Cmm in
  match a.Reg.typ, b.Reg.typ with
  | Int, Int -> a
  | Int, Val -> b
  | Int, Addr -> b
  | Val, Int -> a
  | Val, Val -> a
  | Val, Addr -> b
  | Addr, Int -> a
  | Addr, Addr -> a
  | Addr, Val -> a
  | Float, Float -> a
  | (Int | Addr | Val), Float
  | Float, (Int | Addr | Val) ->
    (* Float unboxing code must be sure to avoid this case. *)
    assert false

(** The set of live registers at a program point.
  * Implemented as a mapping from the physical location to an actual register
  * due to the fact that registers carry additional information and the
  * values in the same location need to be joined at join points.
  *)
module RegSet = struct
  type t = Reg.t RegMap.t

  let union = RegMap.merge (fun _ a b ->
    match a, b with
    | Some _, _ -> a
    | _, _ -> b)

  let diff = RegMap.merge (fun _ a b ->
    match a, b with
    | _, Some _ -> None
    | _, _ -> a)

  let lub = RegMap.merge (fun _ a b ->
    match a, b with
    | None, _ -> b
    | _, None -> a
    | Some ra, Some rb -> Some (reg_lub ra rb))

  let of_array = Array.fold_left (fun acc reg -> RegMap.add reg reg acc) RegMap.empty

  let empty = RegMap.empty

  let equal = RegMap.equal (fun a b -> compare a b = 0)

  let iter f t = RegMap.iter (fun _ v -> f v) t
end

module Problem = struct
  module K = struct
    module S = RegSet

    type t =
      { kill: RegSet.t
      ; gen: RegSet.t
      }

    let dot curr prev =
      { kill = RegSet.union curr.kill prev.kill;
        gen = RegSet.union curr.gen (RegSet.diff prev.gen curr.kill)
      }

    let f s curr = RegSet.union curr.gen (RegSet.diff s curr.kill)
  end

  type t = Cfg.t

  let cfg t = t

  let entry _ _ = RegSet.empty
  let empty _ _ = RegSet.empty

  let kg t id =
    let kill_gen inst destroyed =
      let kill =
        RegSet.union
          (RegSet.of_array inst.Cfg.res)
          (RegSet.of_array (Array.map Proc.phys_reg destroyed))
      in
      let gen = RegSet.of_array inst.Cfg.arg in
      { K.kill; gen }
    in
    match get_inst t id with
    | `Term i -> kill_gen i (Cfg.destroyed_at_terminator i.Cfg.desc)
    | `Basic i -> kill_gen i (Cfg.destroyed_at_basic i.Cfg.desc)
end

module Solver = Make_backward_cfg_solver(Problem)

let update inst id ~solution =
  let live_in, _ = Inst_id.Map.find id solution in
  let live_across = RegSet.diff live_in (RegSet.of_array inst.Cfg.res) in
  Printf.printf "%d:\n\tref" inst.Cfg.id;
  Reg.Set.iter (Printf.printf " %a" Cfg.print_reg) inst.Cfg.live;
  Printf.printf "\n\tacr";
  RegSet.iter (Printf.printf " %a" Cfg.print_reg) live_across;
  Printf.printf "\n\n";
  inst

let run cfg =
  let solution = Solver.solve cfg in
  print_endline (Cfg.fun_name cfg);
  Cfg.iter_blocks cfg ~f:(fun block bb ->
    let body, _ = List.fold_left
      (fun (body, n) i->
        let i' = update i (Inst_id.Inst(block, n)) ~solution in
        i' :: body, n + 1)
      ([], 0)
      bb.body
    in
    let term = update bb.terminator (Inst_id.Term block) ~solution in
    bb.terminator <- term;
    bb.body <- body);
  failwith "stop"
