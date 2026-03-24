open Arch_decl
open X86_decl
open Wsize

module type X86_input = sig

 val call_conv : (register, register_ext, xmm_register, rflag, condt) calling_convention
 val lowering_opt : X86_lowering.lowering_options

end

let atoI decl =
  let open Prog in
  let mk_var k t s =
    V.mk s (Reg(k,Direct)) (Conv.ty_of_cty (Type.atype_of_ltype t)) L._dummy [] in

  match Arch_extra.MkAToIdent.mk decl mk_var with
  | Utils0.Error e ->
      let e = Conv.error_of_cerror (Printer.pp_err ~debug:true) e in
      raise (Utils.HiError e)
  | Utils0.Ok atoI -> atoI

module X86_core = struct
  type reg = register
  type regx = register_ext
  type xreg = xmm_register
  type nonrec rflag = rflag
  type cond = condt
  type asm_op = X86_instr_decl.x86_op
  type extra_op = X86_extra.x86_extra_op
  type lowering_options = X86_lowering.lowering_options

  let atoI = atoI x86_decl
  let asm_e = X86_extra.x86_extra atoI
  let aparams = X86_params.x86_params atoI

  let not_saved_stack = (X86_params.x86_liparams atoI).lip_not_saved_stack

  let pp_asm = Pp_x86.print_prog

  let callstyle = Arch_full.StackDirect

  let known_implicits = ["OF","_of_"; "CF", "_cf_"; "SF", "_sf_"; "ZF", "_zf_"]

  let alloc_stack_need_extra _ = false

  let is_ct_asm_op (o : asm_op) =
    match o with
    | DIV _ | IDIV _ -> false
    | _ -> true

  let is_doit_asm_op (o : asm_op) =
    match o with
    | ADC _ -> true
    | ADCX _ -> true
    | ADD _ -> true
    | ADOX _ -> true
    | AESDEC -> true
    | AESDECLAST -> true
    | AESENC -> true
    | AESENCLAST -> true
    | AESIMC -> true
    | AESKEYGENASSIST -> true
    | AND _ -> true
    | ANDN _ -> true
    | BLENDV (VE8, _) -> true
    | BLENDV _ -> false (* Not DOIT *)
    | BSR _ -> false (* Not DOIT *)
    | BSWAP _ -> false (* Not DOIT *)
    | BT _ -> true
    | BTR _ -> true
    | BTS _ -> true
    | CLC -> false (* Not DOIT *)
    | CLFLUSH -> false (* Not DOIT *)
    | CMOVcc _ -> true
    | CMP _ -> true
    | CQO _ -> false (* Not DOIT *)
    | DEC _ -> true
    | DIV _ -> false (* Not DOIT *)
    | IDIV _ -> false (* Not DOIT *)
    | IMUL _ -> true
    | IMULr _ -> true
    | IMULri _ -> true
    | INC _ -> true
    | LEA _ -> true
    | LFENCE -> false (* Not DOIT *)
    | LZCNT _ -> false (* Not DOIT *)
    | MFENCE -> false (* Not DOIT *)
    | MOV _ -> true
    | MOVD _ -> true
    | MOVEMASK (VE8, _) -> true
    | MOVEMASK _ -> false (* Not DOIT *)
    | MOVSX _ -> true
    | MOVV _ -> true
    | MOVX _ -> true
    | PADD _ -> true
    | POR -> true
    | MOVZX _ -> true
    | MUL _ -> true
    | MULX_lo_hi _ -> true
    | NEG _ -> true
    | NOT _ -> true
    | OR _ -> true
    | PCLMULQDQ -> true
    | PDEP _ -> false (* Not DOIT *)
    | PEXT _ -> false (* Not DOIT *)
    | POPCNT _ -> false (* Not DOIT *)
    | PREFETCHT0 -> false (* Not DOIT *)
    | PREFETCHT1 -> false (* Not DOIT *)
    | PREFETCHT2 -> false (* Not DOIT *)
    | PREFETCHNTA -> false (* Not DOIT *)
    | RCL _ -> false (* Not DOIT *)
    | RCR _ -> false (* Not DOIT *)
    | RDTSC _ -> false (* Not DOIT *)
    | RDTSCP _ -> false (* Not DOIT *)
    | ROL _ -> false (* Not DOIT *)
    | RORX _ -> false (* Not DOIT *)
    | ROR _ -> false (* Not DOIT *)
    | SAL _ -> false (* Not DOIT *)
    | SAR _ -> true
    | SARX _ -> false (* Not DOIT *)
    | SBB _ -> true
    | SETcc -> true
    | SFENCE -> false (* Not DOIT *)
    | SHA256MSG1 -> true
    | SHA256MSG2 -> true
    | SHA256RNDS2 -> true
    | SHL _ -> true
    | SHLD _ -> false (* Not DOIT *)
    | SHLX _ -> true
    | SHR _ -> true
    | SHRD _ -> false (* Not DOIT *)
    | SHRX _ -> true
    | STC -> false (* Not DOIT *)
    | SUB _ -> true
    | TEST _ -> true
    | TZCNT _ -> false (* Not DOIT *)
    | VAESDEC _ -> true
    | VAESDECLAST _ -> true
    | VAESENC _ -> true
    | VAESENCLAST _ -> true
    | VAESIMC -> true
    | VAESKEYGENASSIST -> true
    | VBROADCASTI128 -> true
    | VEXTRACTI128 -> true
    | VINSERTI128 -> true
    | VMOV _ -> true
    | VMOVDQA _ -> true
    | VMOVDQU _ -> true
    | VMOVHPD -> false (* Not DOIT *)
    | VMOVLPD -> false (* Not DOIT *)
    | VMOVSHDUP _ -> true
    | VMOVSLDUP _ -> true
    | VPABS _ -> true
    | VPACKSS _ -> true
    | VPACKUS _ -> true
    | VPADD _ -> true
    | VPALIGNR _ -> true
    | VPAND _ -> true
    | VPANDN _ -> true
    | VPAVG _ -> true
    | VPBLEND _ -> true
    | VPBROADCAST _ -> true
    | VPCLMULQDQ _ -> true
    | VPCMPEQ _ -> true
    | VPCMPGT _ -> true
    | VPERM2I128 -> true
    | VPERMD -> true
    | VPERMQ -> true
    | VPEXTR _ -> true
    | VPINSR _ -> true
    | VPMADDUBSW _ -> true
    | VPMADDWD _ -> true
    | VPMAXS (ve, _) -> ve = VE8 || ve = VE16
    | VPMAXU _ -> true
    | VPMINS (ve, _) -> ve = VE8 || ve = VE16
    | VPMINU _ -> true
    | VPMOVSX _ -> true
    | VPMOVZX _ -> true
    | VPMUL _ -> true
    | VPMULH _ -> true
    | VPMULHRS _ -> true
    | VPMULHU _ -> true
    | VPMULL _ -> true
    | VPMULU _ -> true
    | VPOR _ -> true
    | VPSHUFB _ -> true
    | VPSHUFD _ -> true
    | VPSHUFHW _ -> true
    | VPSHUFLW _ -> true
    | VPSIGN _ -> true
    | VPSLL _ -> true
    | VPSLLDQ _ -> true
    | VPSLLV _ -> true
    | VPSRA _ -> true
    | VPSRL _ -> true
    | VPSRLDQ _ -> true
    | VPSRLV _ -> true
    | VPSUB _ -> true
    | VPTEST _ -> true
    | VPUNPCKH _ -> true
    | VPUNPCKL _ -> true
    | VPXOR _ -> true
    | VSHUFPS _ -> false (* Not DOIT *)
    | XCHG _ -> false (* Not DOIT *)
    | XOR _ -> true

  (* -------------------------------------------------------------------- *)
  (* Rocq printing for x86 asm ops *)

  let pp_ws name fmt ws =
    Format.fprintf fmt "(%s %a)" name ToRocq.pp_wsize ws

  let pp_ws2 name fmt (ws1, ws2) =
    Format.fprintf fmt "(%s %a %a)" name ToRocq.pp_wsize ws1 ToRocq.pp_wsize ws2

  let pp_ve_ws name fmt (ve, ws) =
    Format.fprintf fmt "(%s %a %a)" name ToRocq.pp_velem ve ToRocq.pp_wsize ws

  let pp_ve_ws_ve_ws name fmt (ve1, ws1, ve2, ws2) =
    Format.fprintf fmt "(%s %a %a %a %a)" name
      ToRocq.pp_velem ve1 ToRocq.pp_wsize ws1
      ToRocq.pp_velem ve2 ToRocq.pp_wsize ws2

  let pp_asm_op_for_rocq fmt (o : asm_op) =
    let open X86_instr_decl in
    match o with
    | MOV ws -> pp_ws "MOV" fmt ws
    | MOVSX (ws1, ws2) -> pp_ws2 "MOVSX" fmt (ws1, ws2)
    | MOVZX (ws1, ws2) -> pp_ws2 "MOVZX" fmt (ws1, ws2)
    | CMOVcc ws -> pp_ws "CMOVcc" fmt ws
    | XCHG ws -> pp_ws "XCHG" fmt ws
    | ADD ws -> pp_ws "ADD" fmt ws
    | SUB ws -> pp_ws "SUB" fmt ws
    | MUL ws -> pp_ws "MUL" fmt ws
    | IMUL ws -> pp_ws "IMUL" fmt ws
    | IMULr ws -> pp_ws "IMULr" fmt ws
    | IMULri ws -> pp_ws "IMULri" fmt ws
    | DIV ws -> pp_ws "DIV" fmt ws
    | IDIV ws -> pp_ws "IDIV" fmt ws
    | CQO ws -> pp_ws "CQO" fmt ws
    | ADC ws -> pp_ws "ADC" fmt ws
    | SBB ws -> pp_ws "SBB" fmt ws
    | NEG ws -> pp_ws "NEG" fmt ws
    | INC ws -> pp_ws "INC" fmt ws
    | DEC ws -> pp_ws "DEC" fmt ws
    | LZCNT ws -> pp_ws "LZCNT" fmt ws
    | TZCNT ws -> pp_ws "TZCNT" fmt ws
    | BSR ws -> pp_ws "BSR" fmt ws
    | SETcc -> Format.fprintf fmt "SETcc"
    | BT ws -> pp_ws "BT" fmt ws
    | CLC -> Format.fprintf fmt "CLC"
    | STC -> Format.fprintf fmt "STC"
    | LEA ws -> pp_ws "LEA" fmt ws
    | TEST ws -> pp_ws "TEST" fmt ws
    | CMP ws -> pp_ws "CMP" fmt ws
    | AND ws -> pp_ws "AND" fmt ws
    | ANDN ws -> pp_ws "ANDN" fmt ws
    | OR ws -> pp_ws "OR" fmt ws
    | XOR ws -> pp_ws "XOR" fmt ws
    | NOT ws -> pp_ws "NOT" fmt ws
    | ROR ws -> pp_ws "ROR" fmt ws
    | ROL ws -> pp_ws "ROL" fmt ws
    | RCR ws -> pp_ws "RCR" fmt ws
    | RCL ws -> pp_ws "RCL" fmt ws
    | SHL ws -> pp_ws "SHL" fmt ws
    | SHR ws -> pp_ws "SHR" fmt ws
    | SAL ws -> pp_ws "SAL" fmt ws
    | SAR ws -> pp_ws "SAR" fmt ws
    | SHLD ws -> pp_ws "SHLD" fmt ws
    | SHRD ws -> pp_ws "SHRD" fmt ws
    | RORX ws -> pp_ws "RORX" fmt ws
    | SARX ws -> pp_ws "SARX" fmt ws
    | SHRX ws -> pp_ws "SHRX" fmt ws
    | SHLX ws -> pp_ws "SHLX" fmt ws
    | MULX_lo_hi ws -> pp_ws "MULX_lo_hi" fmt ws
    | ADCX ws -> pp_ws "ADCX" fmt ws
    | ADOX ws -> pp_ws "ADOX" fmt ws
    | BSWAP ws -> pp_ws "BSWAP" fmt ws
    | POPCNT ws -> pp_ws "POPCNT" fmt ws
    | BTR ws -> pp_ws "BTR" fmt ws
    | BTS ws -> pp_ws "BTS" fmt ws
    | PEXT ws -> pp_ws "PEXT" fmt ws
    | PDEP ws -> pp_ws "PDEP" fmt ws
    | MOVX ws -> pp_ws "MOVX" fmt ws
    | POR -> Format.fprintf fmt "POR"
    | PADD (ve, ws) -> pp_ve_ws "PADD" fmt (ve, ws)
    | MOVD ws -> pp_ws "MOVD" fmt ws
    | MOVV ws -> pp_ws "MOVV" fmt ws
    | VMOV ws -> pp_ws "VMOV" fmt ws
    | VMOVDQA ws -> pp_ws "VMOVDQA" fmt ws
    | VMOVDQU ws -> pp_ws "VMOVDQU" fmt ws
    | VPMOVSX (v1, w1, v2, w2) -> pp_ve_ws_ve_ws "VPMOVSX" fmt (v1, w1, v2, w2)
    | VPMOVZX (v1, w1, v2, w2) -> pp_ve_ws_ve_ws "VPMOVZX" fmt (v1, w1, v2, w2)
    | VPAND ws -> pp_ws "VPAND" fmt ws
    | VPANDN ws -> pp_ws "VPANDN" fmt ws
    | VPOR ws -> pp_ws "VPOR" fmt ws
    | VPXOR ws -> pp_ws "VPXOR" fmt ws
    | VPADD (v, w) -> pp_ve_ws "VPADD" fmt (v, w)
    | VPSUB (v, w) -> pp_ve_ws "VPSUB" fmt (v, w)
    | VPAVG (v, w) -> pp_ve_ws "VPAVG" fmt (v, w)
    | VPMULL (v, w) -> pp_ve_ws "VPMULL" fmt (v, w)
    | VPMULH ws -> pp_ws "VPMULH" fmt ws
    | VPMULHU ws -> pp_ws "VPMULHU" fmt ws
    | VPMULHRS ws -> pp_ws "VPMULHRS" fmt ws
    | VPMUL ws -> pp_ws "VPMUL" fmt ws
    | VPMULU ws -> pp_ws "VPMULU" fmt ws
    | VPEXTR ws -> pp_ws "VPEXTR" fmt ws
    | VPINSR ve -> Format.fprintf fmt "(VPINSR %a)" ToRocq.pp_velem ve
    | VPSLL (v, w) -> pp_ve_ws "VPSLL" fmt (v, w)
    | VPSRL (v, w) -> pp_ve_ws "VPSRL" fmt (v, w)
    | VPSRA (v, w) -> pp_ve_ws "VPSRA" fmt (v, w)
    | VPSLLV (v, w) -> pp_ve_ws "VPSLLV" fmt (v, w)
    | VPSRLV (v, w) -> pp_ve_ws "VPSRLV" fmt (v, w)
    | VPSLLDQ ws -> pp_ws "VPSLLDQ" fmt ws
    | VPSRLDQ ws -> pp_ws "VPSRLDQ" fmt ws
    | VPSHUFB ws -> pp_ws "VPSHUFB" fmt ws
    | VPSHUFD ws -> pp_ws "VPSHUFD" fmt ws
    | VPSHUFHW ws -> pp_ws "VPSHUFHW" fmt ws
    | VPSHUFLW ws -> pp_ws "VPSHUFLW" fmt ws
    | VPBLEND (v, w) -> pp_ve_ws "VPBLEND" fmt (v, w)
    | BLENDV (v, w) -> pp_ve_ws "BLENDV" fmt (v, w)
    | VPACKUS (v, w) -> pp_ve_ws "VPACKUS" fmt (v, w)
    | VPACKSS (v, w) -> pp_ve_ws "VPACKSS" fmt (v, w)
    | VSHUFPS ws -> pp_ws "VSHUFPS" fmt ws
    | VPBROADCAST (v, w) -> pp_ve_ws "VPBROADCAST" fmt (v, w)
    | VMOVSHDUP ws -> pp_ws "VMOVSHDUP" fmt ws
    | VMOVSLDUP ws -> pp_ws "VMOVSLDUP" fmt ws
    | VPALIGNR ws -> pp_ws "VPALIGNR" fmt ws
    | VBROADCASTI128 -> Format.fprintf fmt "VBROADCASTI128"
    | VPUNPCKH (v, w) -> pp_ve_ws "VPUNPCKH" fmt (v, w)
    | VPUNPCKL (v, w) -> pp_ve_ws "VPUNPCKL" fmt (v, w)
    | VEXTRACTI128 -> Format.fprintf fmt "VEXTRACTI128"
    | VINSERTI128 -> Format.fprintf fmt "VINSERTI128"
    | VPERM2I128 -> Format.fprintf fmt "VPERM2I128"
    | VPERMD -> Format.fprintf fmt "VPERMD"
    | VPERMQ -> Format.fprintf fmt "VPERMQ"
    | MOVEMASK (v, w) -> pp_ve_ws "MOVEMASK" fmt (v, w)
    | VPCMPEQ (v, w) -> pp_ve_ws "VPCMPEQ" fmt (v, w)
    | VPCMPGT (v, w) -> pp_ve_ws "VPCMPGT" fmt (v, w)
    | VPSIGN (v, w) -> pp_ve_ws "VPSIGN" fmt (v, w)
    | VPMADDUBSW ws -> pp_ws "VPMADDUBSW" fmt ws
    | VPMADDWD ws -> pp_ws "VPMADDWD" fmt ws
    | VMOVLPD -> Format.fprintf fmt "VMOVLPD"
    | VMOVHPD -> Format.fprintf fmt "VMOVHPD"
    | VPMINU (v, w) -> pp_ve_ws "VPMINU" fmt (v, w)
    | VPMINS (v, w) -> pp_ve_ws "VPMINS" fmt (v, w)
    | VPMAXU (v, w) -> pp_ve_ws "VPMAXU" fmt (v, w)
    | VPMAXS (v, w) -> pp_ve_ws "VPMAXS" fmt (v, w)
    | VPABS (v, w) -> pp_ve_ws "VPABS" fmt (v, w)
    | VPTEST ws -> pp_ws "VPTEST" fmt ws
    | CLFLUSH -> Format.fprintf fmt "CLFLUSH"
    | PREFETCHT0 -> Format.fprintf fmt "PREFETCHT0"
    | PREFETCHT1 -> Format.fprintf fmt "PREFETCHT1"
    | PREFETCHT2 -> Format.fprintf fmt "PREFETCHT2"
    | PREFETCHNTA -> Format.fprintf fmt "PREFETCHNTA"
    | LFENCE -> Format.fprintf fmt "LFENCE"
    | MFENCE -> Format.fprintf fmt "MFENCE"
    | SFENCE -> Format.fprintf fmt "SFENCE"
    | RDTSC ws -> pp_ws "RDTSC" fmt ws
    | RDTSCP ws -> pp_ws "RDTSCP" fmt ws
    | AESDEC -> Format.fprintf fmt "AESDEC"
    | VAESDEC ws -> pp_ws "VAESDEC" fmt ws
    | AESDECLAST -> Format.fprintf fmt "AESDECLAST"
    | VAESDECLAST ws -> pp_ws "VAESDECLAST" fmt ws
    | AESENC -> Format.fprintf fmt "AESENC"
    | VAESENC ws -> pp_ws "VAESENC" fmt ws
    | AESENCLAST -> Format.fprintf fmt "AESENCLAST"
    | VAESENCLAST ws -> pp_ws "VAESENCLAST" fmt ws
    | AESIMC -> Format.fprintf fmt "AESIMC"
    | VAESIMC -> Format.fprintf fmt "VAESIMC"
    | AESKEYGENASSIST -> Format.fprintf fmt "AESKEYGENASSIST"
    | VAESKEYGENASSIST -> Format.fprintf fmt "VAESKEYGENASSIST"
    | PCLMULQDQ -> Format.fprintf fmt "PCLMULQDQ"
    | VPCLMULQDQ ws -> pp_ws "VPCLMULQDQ" fmt ws
    | SHA256RNDS2 -> Format.fprintf fmt "SHA256RNDS2"
    | SHA256MSG1 -> Format.fprintf fmt "SHA256MSG1"
    | SHA256MSG2 -> Format.fprintf fmt "SHA256MSG2"

  let pp_reg_kind fmt = function
    | Wsize.Normal -> Format.fprintf fmt "Normal"
    | Wsize.Extra  -> Format.fprintf fmt "Extra"

  let pp_extra_op_for_rocq fmt (o : extra_op) =
    let open X86_extra in
    match o with
    | Oset0 ws -> pp_ws "Oset0" fmt ws
    | Oconcat128 -> Format.fprintf fmt "Oconcat128"
    | Ox86MOVZX32 -> Format.fprintf fmt "Ox86MOVZX32"
    | Ox86MULX ws -> pp_ws "Ox86MULX" fmt ws
    | Ox86MULX_hi ws -> pp_ws "Ox86MULX_hi" fmt ws
    | Ox86SLHinit -> Format.fprintf fmt "Ox86SLHinit"
    | Ox86SLHupdate -> Format.fprintf fmt "Ox86SLHupdate"
    | Ox86SLHmove -> Format.fprintf fmt "Ox86SLHmove"
    | Ox86SLHprotect (rk, ws) ->
      Format.fprintf fmt "(Ox86SLHprotect %a %a)" pp_reg_kind rk ToRocq.pp_wsize ws

  (* All of the extra ops compile into CT instructions (no DIV). *)
  let is_ct_asm_extra (_o : extra_op) = true

  (* All of the extra ops compile into DOIT instructions only, but this needs to be checked manually. *)
  let is_doit_asm_extra (o : extra_op) =
    match o with
    | Oset0 _           -> true
    | Oconcat128        -> true
    | Ox86MOVZX32       -> true
    | Ox86MULX _ws      -> true
    | Ox86MULX_hi _     -> true
    | Ox86SLHinit       -> true
    | Ox86SLHupdate     -> true
    | Ox86SLHmove       -> true
    | Ox86SLHprotect _  -> true

end


module X86 (Lowering_params : X86_input) :
  Arch_full.Core_arch
    with type reg = register
     and type regx = register_ext
     and type xreg = xmm_register
     and type rflag = rflag
     and type cond = condt
     and type asm_op = X86_instr_decl.x86_op
     and type extra_op = X86_extra.x86_extra_op = struct

  include X86_core

  include Lowering_params

end
