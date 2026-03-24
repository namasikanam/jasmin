open Arch_decl
open Riscv_decl

module type Riscv_input = sig
  val call_conv : (register, Arch_utils.empty, Arch_utils.empty, Arch_utils.empty, condt) calling_convention

end

module Riscv_core = struct
  type reg = register
  type regx = Arch_utils.empty
  type xreg = Arch_utils.empty
  type rflag =  Arch_utils.empty
  type cond = condt
  type asm_op = Riscv_instr_decl.riscv_op
  type extra_op = Riscv_extra.riscv_extra_op
  type lowering_options = Riscv_lowering.lowering_options

  let atoI = X86_arch_full.atoI riscv_decl

  let asm_e =  Riscv_extra.riscv_extra atoI
  let aparams = Riscv_params.riscv_params atoI
  let known_implicits = []

  let alloc_stack_need_extra sz =
    not (Riscv_params_core.is_arith_small (Conv.cz_of_z sz))

  (* FIXME RISCV: check if everything is ct *)
  let is_ct_asm_op (o : asm_op) =
    match o with
    | _ -> true

  let is_ct_asm_extra (_o : extra_op) = true

  let is_doit_asm_op (_o : asm_op) = true

  (* All of the extra ops compile into DIT instructions only, but this needs to be checked manually. *)
  let is_doit_asm_extra (_o : extra_op) = true

  let pp_asm_op_for_rocq fmt (o : asm_op) =
    let open Riscv_instr_decl in
    match o with
    | ADD -> Format.fprintf fmt "ADD"
    | ADDI -> Format.fprintf fmt "ADDI"
    | SUB -> Format.fprintf fmt "SUB"
    | SLT -> Format.fprintf fmt "SLT"
    | SLTI -> Format.fprintf fmt "SLTI"
    | SLTU -> Format.fprintf fmt "SLTU"
    | SLTIU -> Format.fprintf fmt "SLTIU"
    | AND -> Format.fprintf fmt "AND"
    | ANDI -> Format.fprintf fmt "ANDI"
    | OR -> Format.fprintf fmt "OR"
    | ORI -> Format.fprintf fmt "ORI"
    | XOR -> Format.fprintf fmt "XOR"
    | XORI -> Format.fprintf fmt "XORI"
    | SLL -> Format.fprintf fmt "SLL"
    | SLLI -> Format.fprintf fmt "SLLI"
    | SRL -> Format.fprintf fmt "SRL"
    | SRLI -> Format.fprintf fmt "SRLI"
    | SRA -> Format.fprintf fmt "SRA"
    | SRAI -> Format.fprintf fmt "SRAI"
    | MV -> Format.fprintf fmt "MV"
    | LA -> Format.fprintf fmt "LA"
    | LI -> Format.fprintf fmt "LI"
    | NOT -> Format.fprintf fmt "NOT"
    | NEG -> Format.fprintf fmt "NEG"
    | LOAD (s, ws) ->
      Format.fprintf fmt "(LOAD %a %a)" ToRocq.pp_signedness s ToRocq.pp_wsize ws
    | STORE ws ->
      Format.fprintf fmt "(STORE %a)" ToRocq.pp_wsize ws
    | MUL -> Format.fprintf fmt "MUL"
    | MULH -> Format.fprintf fmt "MULH"
    | MULHU -> Format.fprintf fmt "MULHU"
    | MULHSU -> Format.fprintf fmt "MULHSU"
    | DIV -> Format.fprintf fmt "DIV"
    | DIVU -> Format.fprintf fmt "DIVU"
    | REM -> Format.fprintf fmt "REM"
    | REMU -> Format.fprintf fmt "REMU"

  let pp_extra_op_for_rocq fmt (o : extra_op) =
    let open Riscv_extra in
    match o with
    | SWAP ws ->
      Format.fprintf fmt "(SWAP %a)" ToRocq.pp_wsize ws
    | Oriscv_add_large_imm ->
      Format.fprintf fmt "Oriscv_add_large_imm"

end

module Riscv (Lowering_params : Riscv_input) : Arch_full.Core_arch
  with type reg = register
   and type regx = Arch_utils.empty
   and type xreg = Arch_utils.empty
   and type rflag = Arch_utils.empty
   and type cond = condt
   and type asm_op = Riscv_instr_decl.riscv_op
   and type extra_op = Riscv_extra.riscv_extra_op = struct
  include Riscv_core
  include Lowering_params

  let lowering_opt = ()

  let not_saved_stack = (Riscv_params.riscv_liparams atoI).lip_not_saved_stack

  let pp_asm = Pp_riscv.print_prog

  let callstyle = Arch_full.ByReg { call = Some RA; return = true }
end
