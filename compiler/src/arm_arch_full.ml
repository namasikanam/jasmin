open Arch_decl
open Arm_decl


module type Arm_input = sig
  val call_conv : (register, Arch_utils.empty, Arch_utils.empty, rflag, condt) calling_convention

end

module Arm_core = struct
  type reg = register
  type regx = Arch_utils.empty
  type xreg = Arch_utils.empty
  type nonrec rflag = rflag
  type cond = condt
  type asm_op = Arm_instr_decl.arm_op
  type extra_op = Arm_extra.arm_extra_op
  type lowering_options = Arm_lowering.lowering_options

  let atoI = X86_arch_full.atoI arm_decl

  let asm_e = Arm_extra.arm_extra atoI
  let aparams = Arm_params.arm_params atoI

  let known_implicits = ["NF", "_nf_"; "ZF", "_zf_"; "CF", "_cf_"; "VF", "_vf_"]

  let alloc_stack_need_extra sz =
    not (Arm_params_core.is_arith_small (Conv.cz_of_z sz))

  let is_ct_asm_op (o : asm_op) =
    match o with
    | ARM_op( (SDIV  | UDIV), _) -> false
    | _ -> true

  let is_doit_asm_op (o : asm_op) =
    match o with
    | ARM_op(ADC, _) -> true
    | ARM_op(ADD, _) -> true
    | ARM_op(ADR, _) -> false (* Not DIT *)
    | ARM_op(AND, _) -> true
    | ARM_op(ASR, _) -> true
    | ARM_op(BFC, _) -> true
    | ARM_op(BFI, _) -> true
    | ARM_op(BIC, _) -> true
    | ARM_op(CLZ, _) -> true
    | ARM_op(CMN, _) -> true
    | ARM_op(CMP, _) -> true
    | ARM_op(EOR, _) -> true
    | ARM_op(LDR, _) -> true
    | ARM_op(LDRB, _) -> true
    | ARM_op(LDRH, _) -> true
    | ARM_op(LDRSB, _) -> true
    | ARM_op(LDRSH, _) -> true
    | ARM_op(LSL, _) -> true
    | ARM_op(LSR, _) -> true
    | ARM_op(MLA, _) -> true
    | ARM_op(MLS, _) -> true
    | ARM_op(MOV, _) -> true
    | ARM_op(MOVT, _) -> true
    | ARM_op(MUL, _) -> true
    | ARM_op(MVN, _) -> true
    | ARM_op(ORR, _) -> true
    | ARM_op(REV, _) -> true
    | ARM_op(REV16, _) -> true
    | ARM_op(REVSH, _) -> false (* Not DIT *)
    | ARM_op(ROR, _) -> true
    | ARM_op(RSB, _) -> false (* Not DIT *)
    | ARM_op(SBC, _) -> true
    | ARM_op(SBFX, _) -> true
    | ARM_op(SDIV, _) -> false (* Not DIT *)
    | ARM_op(SMLA_hw _, _) -> false (* Not DIT *)
    | ARM_op(SMLAL, _) -> true
    | ARM_op(SMMUL, _) -> false (* Not DIT *)
    | ARM_op(SMMULR, _) -> false (* Not DIT *)
    | ARM_op(SMUL_hw _, _) -> false (* Not DIT *)
    | ARM_op(SMULL, _) -> true
    | ARM_op(SMULW_hw _, _) -> false (* Not DIT *)
    | ARM_op(STR, _) -> true
    | ARM_op(STRB, _) -> true
    | ARM_op(STRH, _) -> true
    | ARM_op(SUB, _) -> true
    | ARM_op(TST, _) -> true
    | ARM_op(UBFX, _) -> true
    | ARM_op(UDIV, _) -> false (* Not DIT *)
    | ARM_op(UMAAL, _) -> false (* Not DIT *)
    | ARM_op(UMLAL, _) -> true
    | ARM_op(UMULL, _) -> true
    | ARM_op(UXTB, _) -> true
    | ARM_op(UXTH, _) -> true


  (* All of the extra ops compile into CT instructions (no DIV). *)
  let is_ct_asm_extra (_o : extra_op) = true

  (* All of the extra ops compile into DIT instructions only, but this needs to be checked manually. *)
  let is_doit_asm_extra (o : extra_op) =
    match o with
    | Oarm_swap _ -> true
    | Oarm_add_large_imm -> true
    | (Osmart_li _ | Osmart_li_cc _) -> true (* emit MOVT *)

  let pp_halfword fmt = function
    | Arm_instr_decl.HWB -> Format.fprintf fmt "HWB"
    | Arm_instr_decl.HWT -> Format.fprintf fmt "HWT"

  let pp_shift_kind fmt = function
    | Shift_kind.SLSL -> Format.fprintf fmt "SLSL"
    | Shift_kind.SLSR -> Format.fprintf fmt "SLSR"
    | Shift_kind.SASR -> Format.fprintf fmt "SASR"
    | Shift_kind.SROR -> Format.fprintf fmt "SROR"

  let pp_arm_options fmt (o : Arm_instr_decl.arm_options) =
    Format.fprintf fmt "{| set_flags := %b; is_conditional := %b; has_shift := %a |}"
      o.set_flags o.is_conditional
      (ToRocq.pp_option (fun fmt sk -> Format.fprintf fmt "%a" pp_shift_kind sk))
      o.has_shift

  let pp_arm_mnemonic fmt (m : Arm_instr_decl.arm_mnemonic) =
    let open Arm_instr_decl in
    match m with
    | ADD -> Format.fprintf fmt "ADD"
    | ADC -> Format.fprintf fmt "ADC"
    | MUL -> Format.fprintf fmt "MUL"
    | MLA -> Format.fprintf fmt "MLA"
    | MLS -> Format.fprintf fmt "MLS"
    | SDIV -> Format.fprintf fmt "SDIV"
    | SUB -> Format.fprintf fmt "SUB"
    | SBC -> Format.fprintf fmt "SBC"
    | RSB -> Format.fprintf fmt "RSB"
    | UDIV -> Format.fprintf fmt "UDIV"
    | UMULL -> Format.fprintf fmt "UMULL"
    | UMAAL -> Format.fprintf fmt "UMAAL"
    | UMLAL -> Format.fprintf fmt "UMLAL"
    | SMULL -> Format.fprintf fmt "SMULL"
    | SMLAL -> Format.fprintf fmt "SMLAL"
    | SMMUL -> Format.fprintf fmt "SMMUL"
    | SMMULR -> Format.fprintf fmt "SMMULR"
    | SMUL_hw (h1, h2) ->
      Format.fprintf fmt "(SMUL_hw %a %a)" pp_halfword h1 pp_halfword h2
    | SMLA_hw (h1, h2) ->
      Format.fprintf fmt "(SMLA_hw %a %a)" pp_halfword h1 pp_halfword h2
    | SMULW_hw h ->
      Format.fprintf fmt "(SMULW_hw %a)" pp_halfword h
    | AND -> Format.fprintf fmt "AND"
    | BFC -> Format.fprintf fmt "BFC"
    | BFI -> Format.fprintf fmt "BFI"
    | BIC -> Format.fprintf fmt "BIC"
    | EOR -> Format.fprintf fmt "EOR"
    | MVN -> Format.fprintf fmt "MVN"
    | ORR -> Format.fprintf fmt "ORR"
    | ASR -> Format.fprintf fmt "ASR"
    | LSL -> Format.fprintf fmt "LSL"
    | LSR -> Format.fprintf fmt "LSR"
    | ROR -> Format.fprintf fmt "ROR"
    | REV -> Format.fprintf fmt "REV"
    | REV16 -> Format.fprintf fmt "REV16"
    | REVSH -> Format.fprintf fmt "REVSH"
    | ADR -> Format.fprintf fmt "ADR"
    | MOV -> Format.fprintf fmt "MOV"
    | MOVT -> Format.fprintf fmt "MOVT"
    | UBFX -> Format.fprintf fmt "UBFX"
    | UXTB -> Format.fprintf fmt "UXTB"
    | UXTH -> Format.fprintf fmt "UXTH"
    | SBFX -> Format.fprintf fmt "SBFX"
    | CLZ -> Format.fprintf fmt "CLZ"
    | CMP -> Format.fprintf fmt "CMP"
    | TST -> Format.fprintf fmt "TST"
    | CMN -> Format.fprintf fmt "CMN"
    | LDR -> Format.fprintf fmt "LDR"
    | LDRB -> Format.fprintf fmt "LDRB"
    | LDRH -> Format.fprintf fmt "LDRH"
    | LDRSB -> Format.fprintf fmt "LDRSB"
    | LDRSH -> Format.fprintf fmt "LDRSH"
    | STR -> Format.fprintf fmt "STR"
    | STRB -> Format.fprintf fmt "STRB"
    | STRH -> Format.fprintf fmt "STRH"

  let pp_asm_op_for_rocq fmt (o : asm_op) =
    let Arm_instr_decl.ARM_op (m, opts) = o in
    Format.fprintf fmt "(ARM_op %a %a)" pp_arm_mnemonic m pp_arm_options opts

  let pp_extra_op_for_rocq fmt (o : extra_op) =
    let open Arm_extra in
    match o with
    | Oarm_swap ws ->
      Format.fprintf fmt "(Oarm_swap %a)" ToRocq.pp_wsize ws
    | Oarm_add_large_imm ->
      Format.fprintf fmt "Oarm_add_large_imm"
    | Osmart_li ws ->
      Format.fprintf fmt "(Osmart_li %a)" ToRocq.pp_wsize ws
    | Osmart_li_cc ws ->
      Format.fprintf fmt "(Osmart_li_cc %a)" ToRocq.pp_wsize ws

end

module Arm (Lowering_params : Arm_input) : Arch_full.Core_arch
  with type reg = register
   and type regx = Arch_utils.empty
   and type xreg = Arch_utils.empty
   and type rflag = rflag
   and type cond = condt
   and type asm_op = Arm_instr_decl.arm_op
   and type extra_op = Arm_extra.arm_extra_op = struct
  include Arm_core
  include Lowering_params

  (* TODO_ARM: r9 is a platform register. (cf. arch_decl)
     Here we assume it's just a variable register. *)

  let lowering_opt = ()

  let not_saved_stack = (Arm_params.arm_liparams atoI).lip_not_saved_stack

  let pp_asm = Pp_arm_m4.print_prog

  let callstyle = Arch_full.ByReg { call = Some LR; return = false }
end
