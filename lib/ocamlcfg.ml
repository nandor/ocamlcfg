[@@@ocaml.warning "+a-30-40-41-42"]

module Label = Label

module Cfg = struct
  include Cfg

  module Basic_block = struct
    type t = basic_block

    let start t = t.start

    let body t = t.body

    let terminator t = t.terminator

    let is_exit = Cfg.is_exit
  end

  let all_successor_labels t b =
    successor_labels t ~normal:true ~exn:true b |> Label.Set.elements

  let successor_labels t b =
    successor_labels t ~normal:true ~exn:false b |> Label.Set.elements
end

module Cfg_with_layout = struct
  include Cfg_with_layout

  let eliminate_dead_blocks = Eliminate_dead_blocks.run

  (* eliminate fallthrough implies dead block elimination *)
  let eliminate_fallthrough_blocks = Eliminate_fallthrough_blocks.run

  let of_linear = Linear_to_cfg.run

  let to_linear = Cfg_to_linear.run
end

module Passes = struct
  let simplify_terminators = Simplify_terminator.run

  let add_extra_debug = Extra_debug.add

  let slot_to_register = Slot_to_register.run

  let liveness = Liveness.run

  let remove_dead_spills = Liveness.run
end

module Util = struct
  let verbose = Cfg.verbose

  let print_linear = Cfg_to_linear.print_linear

  let print_assembly = Cfg_to_linear.print_assembly
end

module Analysis = struct
  include Data_flow_analysis
end
