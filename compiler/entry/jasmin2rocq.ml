open Jasmin
open Cmdliner
open CommonCLI
open Utils

module F = Format

(* -------------------------------------------------------------------- *)
(* Architecture-specific asm_op printers for Rocq *)
(* TODO None of this should be here, the architecture-specific parts go in
   arch_full and generic parts in src *)

(* TODO This is not architecture specific *)
let pp_wsize fmt = function
  | Wsize.U8   -> F.fprintf fmt "U8"
  | Wsize.U16  -> F.fprintf fmt "U16"
  | Wsize.U32  -> F.fprintf fmt "U32"
  | Wsize.U64  -> F.fprintf fmt "U64"
  | Wsize.U128 -> F.fprintf fmt "U128"
  | Wsize.U256 -> F.fprintf fmt "U256"

(* TODO This is not architecture specific *)
let pp_velem fmt = function
  | Wsize.VE8  -> F.fprintf fmt "VE8"
  | Wsize.VE16 -> F.fprintf fmt "VE16"
  | Wsize.VE32 -> F.fprintf fmt "VE32"
  | Wsize.VE64 -> F.fprintf fmt "VE64"

(* Helper for constructors with one wsize arg *)
let pp_ws name fmt ws =
  F.fprintf fmt "(%s %a)" name pp_wsize ws

(* Helper for constructors with two wsize args *)
let pp_ws2 name fmt (ws1, ws2) =
  F.fprintf fmt "(%s %a %a)" name pp_wsize ws1 pp_wsize ws2

(* Helper for constructors with velem * wsize args *)
let pp_ve_ws name fmt (ve, ws) =
  F.fprintf fmt "(%s %a %a)" name pp_velem ve pp_wsize ws

(* Helper for constructors with velem * wsize * velem * wsize args *)
let pp_ve_ws_ve_ws name fmt (ve1, ws1, ve2, ws2) =
  F.fprintf fmt "(%s %a %a %a %a)" name pp_velem ve1 pp_wsize ws1 pp_velem ve2 pp_wsize ws2

let pp_reg_kind fmt = function
  | Wsize.Normal -> F.fprintf fmt "Normal"
  | Wsize.Extra  -> F.fprintf fmt "Extra"

(* TODO
   - move the the argument printer (e.g., [pp_ws]) as an argument and have only
     one [pp_base] function
   - if [pp_ws] and the rest take tuples instead of separate arguments there is
     no need to destruct the arguments of each constructor (e.g.,
     [MOVSX a -> pp_base_ws2 msb "MOVSX" fmt a])
   - The pp_base function should use a printer for option types defined in torocq
   - Move the printing of x86_op (e.g., [MOV ws]) and extra ops as separate
     functions and then make this function architecture generic
   - The printers for x86_op and extra ops should go in full_arch or something
     like that
   - Why the special case for [VPINSR]? *)
let pp_x86_op fmt (o : (_, _, _, _, _, X86_instr_decl.x86_op, X86_extra.x86_extra_op) Arch_extra.extended_op) =
  let pp_base msb name fmt = match msb with
    | None   -> F.fprintf fmt "(BaseOp (None, %s))" name
    | Some w -> F.fprintf fmt "(BaseOp (Some %a, %s))" pp_wsize w name in
  let pp_base_ws msb name fmt ws = match msb with
    | None   -> F.fprintf fmt "(BaseOp (None, %a))" (pp_ws name) ws
    | Some w -> F.fprintf fmt "(BaseOp (Some %a, %a))" pp_wsize w (pp_ws name) ws in
  let pp_base_ws2 msb name fmt ws1 ws2 = match msb with
    | None   -> F.fprintf fmt "(BaseOp (None, %a))" (pp_ws2 name) (ws1, ws2)
    | Some w -> F.fprintf fmt "(BaseOp (Some %a, %a))" pp_wsize w (pp_ws2 name) (ws1, ws2) in
  let pp_base_ve_ws msb name fmt ve ws = match msb with
    | None   -> F.fprintf fmt "(BaseOp (None, %a))" (pp_ve_ws name) (ve, ws)
    | Some w -> F.fprintf fmt "(BaseOp (Some %a, %a))" pp_wsize w (pp_ve_ws name) (ve, ws) in
  let pp_base_ve_ws_ve_ws msb name fmt ve1 ws1 ve2 ws2 = match msb with
    | None   -> F.fprintf fmt "(BaseOp (None, %a))" (pp_ve_ws_ve_ws name) (ve1, ws1, ve2, ws2)
    | Some w -> F.fprintf fmt "(BaseOp (Some %a, %a))" pp_wsize w (pp_ve_ws_ve_ws name) (ve1, ws1, ve2, ws2) in
  match o with
  (* BaseOp: x86_op *)
  | BaseOp (msb, MOV ws) -> pp_base_ws msb "MOV" fmt ws
  | BaseOp (msb, MOVSX (ws1, ws2)) -> pp_base_ws2 msb "MOVSX" fmt ws1 ws2
  | BaseOp (msb, MOVZX (ws1, ws2)) -> pp_base_ws2 msb "MOVZX" fmt ws1 ws2
  | BaseOp (msb, CMOVcc ws) -> pp_base_ws msb "CMOVcc" fmt ws
  | BaseOp (msb, XCHG ws) -> pp_base_ws msb "XCHG" fmt ws
  | BaseOp (msb, ADD ws) -> pp_base_ws msb "ADD" fmt ws
  | BaseOp (msb, SUB ws) -> pp_base_ws msb "SUB" fmt ws
  | BaseOp (msb, MUL ws) -> pp_base_ws msb "MUL" fmt ws
  | BaseOp (msb, IMUL ws) -> pp_base_ws msb "IMUL" fmt ws
  | BaseOp (msb, IMULr ws) -> pp_base_ws msb "IMULr" fmt ws
  | BaseOp (msb, IMULri ws) -> pp_base_ws msb "IMULri" fmt ws
  | BaseOp (msb, DIV ws) -> pp_base_ws msb "DIV" fmt ws
  | BaseOp (msb, IDIV ws) -> pp_base_ws msb "IDIV" fmt ws
  | BaseOp (msb, CQO ws) -> pp_base_ws msb "CQO" fmt ws
  | BaseOp (msb, ADC ws) -> pp_base_ws msb "ADC" fmt ws
  | BaseOp (msb, SBB ws) -> pp_base_ws msb "SBB" fmt ws
  | BaseOp (msb, NEG ws) -> pp_base_ws msb "NEG" fmt ws
  | BaseOp (msb, INC ws) -> pp_base_ws msb "INC" fmt ws
  | BaseOp (msb, DEC ws) -> pp_base_ws msb "DEC" fmt ws
  | BaseOp (msb, LZCNT ws) -> pp_base_ws msb "LZCNT" fmt ws
  | BaseOp (msb, TZCNT ws) -> pp_base_ws msb "TZCNT" fmt ws
  | BaseOp (msb, BSR ws) -> pp_base_ws msb "BSR" fmt ws
  | BaseOp (msb, SETcc) -> pp_base msb "SETcc" fmt
  | BaseOp (msb, BT ws) -> pp_base_ws msb "BT" fmt ws
  | BaseOp (msb, CLC) -> pp_base msb "CLC" fmt
  | BaseOp (msb, STC) -> pp_base msb "STC" fmt
  | BaseOp (msb, LEA ws) -> pp_base_ws msb "LEA" fmt ws
  | BaseOp (msb, TEST ws) -> pp_base_ws msb "TEST" fmt ws
  | BaseOp (msb, CMP ws) -> pp_base_ws msb "CMP" fmt ws
  | BaseOp (msb, AND ws) -> pp_base_ws msb "AND" fmt ws
  | BaseOp (msb, ANDN ws) -> pp_base_ws msb "ANDN" fmt ws
  | BaseOp (msb, OR ws) -> pp_base_ws msb "OR" fmt ws
  | BaseOp (msb, XOR ws) -> pp_base_ws msb "XOR" fmt ws
  | BaseOp (msb, NOT ws) -> pp_base_ws msb "NOT" fmt ws
  | BaseOp (msb, ROR ws) -> pp_base_ws msb "ROR" fmt ws
  | BaseOp (msb, ROL ws) -> pp_base_ws msb "ROL" fmt ws
  | BaseOp (msb, RCR ws) -> pp_base_ws msb "RCR" fmt ws
  | BaseOp (msb, RCL ws) -> pp_base_ws msb "RCL" fmt ws
  | BaseOp (msb, SHL ws) -> pp_base_ws msb "SHL" fmt ws
  | BaseOp (msb, SHR ws) -> pp_base_ws msb "SHR" fmt ws
  | BaseOp (msb, SAL ws) -> pp_base_ws msb "SAL" fmt ws
  | BaseOp (msb, SAR ws) -> pp_base_ws msb "SAR" fmt ws
  | BaseOp (msb, SHLD ws) -> pp_base_ws msb "SHLD" fmt ws
  | BaseOp (msb, SHRD ws) -> pp_base_ws msb "SHRD" fmt ws
  | BaseOp (msb, RORX ws) -> pp_base_ws msb "RORX" fmt ws
  | BaseOp (msb, SARX ws) -> pp_base_ws msb "SARX" fmt ws
  | BaseOp (msb, SHRX ws) -> pp_base_ws msb "SHRX" fmt ws
  | BaseOp (msb, SHLX ws) -> pp_base_ws msb "SHLX" fmt ws
  | BaseOp (msb, MULX_lo_hi ws) -> pp_base_ws msb "MULX_lo_hi" fmt ws
  | BaseOp (msb, ADCX ws) -> pp_base_ws msb "ADCX" fmt ws
  | BaseOp (msb, ADOX ws) -> pp_base_ws msb "ADOX" fmt ws
  | BaseOp (msb, BSWAP ws) -> pp_base_ws msb "BSWAP" fmt ws
  | BaseOp (msb, POPCNT ws) -> pp_base_ws msb "POPCNT" fmt ws
  | BaseOp (msb, BTR ws) -> pp_base_ws msb "BTR" fmt ws
  | BaseOp (msb, BTS ws) -> pp_base_ws msb "BTS" fmt ws
  | BaseOp (msb, PEXT ws) -> pp_base_ws msb "PEXT" fmt ws
  | BaseOp (msb, PDEP ws) -> pp_base_ws msb "PDEP" fmt ws
  | BaseOp (msb, MOVX ws) -> pp_base_ws msb "MOVX" fmt ws
  | BaseOp (msb, POR) -> pp_base msb "POR" fmt
  | BaseOp (msb, PADD (ve, ws)) -> pp_base_ve_ws msb "PADD" fmt ve ws
  | BaseOp (msb, MOVD ws) -> pp_base_ws msb "MOVD" fmt ws
  | BaseOp (msb, MOVV ws) -> pp_base_ws msb "MOVV" fmt ws
  | BaseOp (msb, VMOV ws) -> pp_base_ws msb "VMOV" fmt ws
  | BaseOp (msb, VMOVDQA ws) -> pp_base_ws msb "VMOVDQA" fmt ws
  | BaseOp (msb, VMOVDQU ws) -> pp_base_ws msb "VMOVDQU" fmt ws
  | BaseOp (msb, VPMOVSX (ve1, ws1, ve2, ws2)) -> pp_base_ve_ws_ve_ws msb "VPMOVSX" fmt ve1 ws1 ve2 ws2
  | BaseOp (msb, VPMOVZX (ve1, ws1, ve2, ws2)) -> pp_base_ve_ws_ve_ws msb "VPMOVZX" fmt ve1 ws1 ve2 ws2
  | BaseOp (msb, VPAND ws) -> pp_base_ws msb "VPAND" fmt ws
  | BaseOp (msb, VPANDN ws) -> pp_base_ws msb "VPANDN" fmt ws
  | BaseOp (msb, VPOR ws) -> pp_base_ws msb "VPOR" fmt ws
  | BaseOp (msb, VPXOR ws) -> pp_base_ws msb "VPXOR" fmt ws
  | BaseOp (msb, VPADD (ve, ws)) -> pp_base_ve_ws msb "VPADD" fmt ve ws
  | BaseOp (msb, VPSUB (ve, ws)) -> pp_base_ve_ws msb "VPSUB" fmt ve ws
  | BaseOp (msb, VPAVG (ve, ws)) -> pp_base_ve_ws msb "VPAVG" fmt ve ws
  | BaseOp (msb, VPMULL (ve, ws)) -> pp_base_ve_ws msb "VPMULL" fmt ve ws
  | BaseOp (msb, VPMULH ws) -> pp_base_ws msb "VPMULH" fmt ws
  | BaseOp (msb, VPMULHU ws) -> pp_base_ws msb "VPMULHU" fmt ws
  | BaseOp (msb, VPMULHRS ws) -> pp_base_ws msb "VPMULHRS" fmt ws
  | BaseOp (msb, VPMUL ws) -> pp_base_ws msb "VPMUL" fmt ws
  | BaseOp (msb, VPMULU ws) -> pp_base_ws msb "VPMULU" fmt ws
  | BaseOp (msb, VPEXTR ws) -> pp_base_ws msb "VPEXTR" fmt ws
  | BaseOp (msb, VPINSR ve) ->
    (match msb with
     | None   -> F.fprintf fmt "(BaseOp (None, (VPINSR %a)))" pp_velem ve
     | Some w -> F.fprintf fmt "(BaseOp (Some %a, (VPINSR %a)))" pp_wsize w pp_velem ve)
  | BaseOp (msb, VPSLL (ve, ws)) -> pp_base_ve_ws msb "VPSLL" fmt ve ws
  | BaseOp (msb, VPSRL (ve, ws)) -> pp_base_ve_ws msb "VPSRL" fmt ve ws
  | BaseOp (msb, VPSRA (ve, ws)) -> pp_base_ve_ws msb "VPSRA" fmt ve ws
  | BaseOp (msb, VPSLLV (ve, ws)) -> pp_base_ve_ws msb "VPSLLV" fmt ve ws
  | BaseOp (msb, VPSRLV (ve, ws)) -> pp_base_ve_ws msb "VPSRLV" fmt ve ws
  | BaseOp (msb, VPSLLDQ ws) -> pp_base_ws msb "VPSLLDQ" fmt ws
  | BaseOp (msb, VPSRLDQ ws) -> pp_base_ws msb "VPSRLDQ" fmt ws
  | BaseOp (msb, VPSHUFB ws) -> pp_base_ws msb "VPSHUFB" fmt ws
  | BaseOp (msb, VPSHUFD ws) -> pp_base_ws msb "VPSHUFD" fmt ws
  | BaseOp (msb, VPSHUFHW ws) -> pp_base_ws msb "VPSHUFHW" fmt ws
  | BaseOp (msb, VPSHUFLW ws) -> pp_base_ws msb "VPSHUFLW" fmt ws
  | BaseOp (msb, VPBLEND (ve, ws)) -> pp_base_ve_ws msb "VPBLEND" fmt ve ws
  | BaseOp (msb, BLENDV (ve, ws)) -> pp_base_ve_ws msb "BLENDV" fmt ve ws
  | BaseOp (msb, VPACKUS (ve, ws)) -> pp_base_ve_ws msb "VPACKUS" fmt ve ws
  | BaseOp (msb, VPACKSS (ve, ws)) -> pp_base_ve_ws msb "VPACKSS" fmt ve ws
  | BaseOp (msb, VSHUFPS ws) -> pp_base_ws msb "VSHUFPS" fmt ws
  | BaseOp (msb, VPBROADCAST (ve, ws)) -> pp_base_ve_ws msb "VPBROADCAST" fmt ve ws
  | BaseOp (msb, VMOVSHDUP ws) -> pp_base_ws msb "VMOVSHDUP" fmt ws
  | BaseOp (msb, VMOVSLDUP ws) -> pp_base_ws msb "VMOVSLDUP" fmt ws
  | BaseOp (msb, VPALIGNR ws) -> pp_base_ws msb "VPALIGNR" fmt ws
  | BaseOp (msb, VBROADCASTI128) -> pp_base msb "VBROADCASTI128" fmt
  | BaseOp (msb, VPUNPCKH (ve, ws)) -> pp_base_ve_ws msb "VPUNPCKH" fmt ve ws
  | BaseOp (msb, VPUNPCKL (ve, ws)) -> pp_base_ve_ws msb "VPUNPCKL" fmt ve ws
  | BaseOp (msb, VEXTRACTI128) -> pp_base msb "VEXTRACTI128" fmt
  | BaseOp (msb, VINSERTI128) -> pp_base msb "VINSERTI128" fmt
  | BaseOp (msb, VPERM2I128) -> pp_base msb "VPERM2I128" fmt
  | BaseOp (msb, VPERMD) -> pp_base msb "VPERMD" fmt
  | BaseOp (msb, VPERMQ) -> pp_base msb "VPERMQ" fmt
  | BaseOp (msb, MOVEMASK (ve, ws)) -> pp_base_ve_ws msb "MOVEMASK" fmt ve ws
  | BaseOp (msb, VPCMPEQ (ve, ws)) -> pp_base_ve_ws msb "VPCMPEQ" fmt ve ws
  | BaseOp (msb, VPCMPGT (ve, ws)) -> pp_base_ve_ws msb "VPCMPGT" fmt ve ws
  | BaseOp (msb, VPSIGN (ve, ws)) -> pp_base_ve_ws msb "VPSIGN" fmt ve ws
  | BaseOp (msb, VPMADDUBSW ws) -> pp_base_ws msb "VPMADDUBSW" fmt ws
  | BaseOp (msb, VPMADDWD ws) -> pp_base_ws msb "VPMADDWD" fmt ws
  | BaseOp (msb, VMOVLPD) -> pp_base msb "VMOVLPD" fmt
  | BaseOp (msb, VMOVHPD) -> pp_base msb "VMOVHPD" fmt
  | BaseOp (msb, VPMINU (ve, ws)) -> pp_base_ve_ws msb "VPMINU" fmt ve ws
  | BaseOp (msb, VPMINS (ve, ws)) -> pp_base_ve_ws msb "VPMINS" fmt ve ws
  | BaseOp (msb, VPMAXU (ve, ws)) -> pp_base_ve_ws msb "VPMAXU" fmt ve ws
  | BaseOp (msb, VPMAXS (ve, ws)) -> pp_base_ve_ws msb "VPMAXS" fmt ve ws
  | BaseOp (msb, VPABS (ve, ws)) -> pp_base_ve_ws msb "VPABS" fmt ve ws
  | BaseOp (msb, VPTEST ws) -> pp_base_ws msb "VPTEST" fmt ws
  | BaseOp (msb, CLFLUSH) -> pp_base msb "CLFLUSH" fmt
  | BaseOp (msb, PREFETCHT0) -> pp_base msb "PREFETCHT0" fmt
  | BaseOp (msb, PREFETCHT1) -> pp_base msb "PREFETCHT1" fmt
  | BaseOp (msb, PREFETCHT2) -> pp_base msb "PREFETCHT2" fmt
  | BaseOp (msb, PREFETCHNTA) -> pp_base msb "PREFETCHNTA" fmt
  | BaseOp (msb, LFENCE) -> pp_base msb "LFENCE" fmt
  | BaseOp (msb, MFENCE) -> pp_base msb "MFENCE" fmt
  | BaseOp (msb, SFENCE) -> pp_base msb "SFENCE" fmt
  | BaseOp (msb, RDTSC ws) -> pp_base_ws msb "RDTSC" fmt ws
  | BaseOp (msb, RDTSCP ws) -> pp_base_ws msb "RDTSCP" fmt ws
  | BaseOp (msb, AESDEC) -> pp_base msb "AESDEC" fmt
  | BaseOp (msb, VAESDEC ws) -> pp_base_ws msb "VAESDEC" fmt ws
  | BaseOp (msb, AESDECLAST) -> pp_base msb "AESDECLAST" fmt
  | BaseOp (msb, VAESDECLAST ws) -> pp_base_ws msb "VAESDECLAST" fmt ws
  | BaseOp (msb, AESENC) -> pp_base msb "AESENC" fmt
  | BaseOp (msb, VAESENC ws) -> pp_base_ws msb "VAESENC" fmt ws
  | BaseOp (msb, AESENCLAST) -> pp_base msb "AESENCLAST" fmt
  | BaseOp (msb, VAESENCLAST ws) -> pp_base_ws msb "VAESENCLAST" fmt ws
  | BaseOp (msb, AESIMC) -> pp_base msb "AESIMC" fmt
  | BaseOp (msb, VAESIMC) -> pp_base msb "VAESIMC" fmt
  | BaseOp (msb, AESKEYGENASSIST) -> pp_base msb "AESKEYGENASSIST" fmt
  | BaseOp (msb, VAESKEYGENASSIST) -> pp_base msb "VAESKEYGENASSIST" fmt
  | BaseOp (msb, PCLMULQDQ) -> pp_base msb "PCLMULQDQ" fmt
  | BaseOp (msb, VPCLMULQDQ ws) -> pp_base_ws msb "VPCLMULQDQ" fmt ws
  | BaseOp (msb, SHA256RNDS2) -> pp_base msb "SHA256RNDS2" fmt
  | BaseOp (msb, SHA256MSG1) -> pp_base msb "SHA256MSG1" fmt
  | BaseOp (msb, SHA256MSG2) -> pp_base msb "SHA256MSG2" fmt
  (* ExtOp: x86_extra_op *)
  | ExtOp (Oset0 ws) -> F.fprintf fmt "(ExtOp %a)" (pp_ws "Oset0") ws
  | ExtOp Oconcat128 -> F.fprintf fmt "(ExtOp Oconcat128)"
  | ExtOp Ox86MOVZX32 -> F.fprintf fmt "(ExtOp Ox86MOVZX32)"
  | ExtOp (Ox86MULX ws) -> F.fprintf fmt "(ExtOp %a)" (pp_ws "Ox86MULX") ws
  | ExtOp (Ox86MULX_hi ws) -> F.fprintf fmt "(ExtOp %a)" (pp_ws "Ox86MULX_hi") ws
  | ExtOp Ox86SLHinit -> F.fprintf fmt "(ExtOp Ox86SLHinit)"
  | ExtOp Ox86SLHupdate -> F.fprintf fmt "(ExtOp Ox86SLHupdate)"
  | ExtOp Ox86SLHmove -> F.fprintf fmt "(ExtOp Ox86SLHmove)"
  | ExtOp (Ox86SLHprotect (rk, ws)) ->
    F.fprintf fmt "(ExtOp (Ox86SLHprotect %a %a))" pp_reg_kind rk pp_wsize ws

(* -------------------------------------------------------------------- *)

let parse_and_extract arch call_conv idirs =
  let module A = (val CoreArchFactory.get_arch_module arch call_conv) in
  let extract output pass file warn =
    if not warn then nowarning ();
    let prog =
      parse_and_compile (module A) ~wi2i:false pass file idirs (* TODO why false wi2i? *)
    in
    let fmt, close =
      match output with
      | None -> (Format.std_formatter, fun () -> ())
      | Some f ->
          let out = open_out f in
          let fmt = Format.formatter_of_out_channel out in
          (fmt, fun () -> close_out out)
    in
    (try
       ToRocq.extract prog arch A.reg_size A.msf_size A.asmOp
         (Obj.magic pp_x86_op) fmt; (* TODO use modules to avoid Obj.magic *)
       close ()
     with e ->
       BatPervasives.ignore_exceptions (fun () -> close ()) ();
       raise e)
  in
  fun output pass file warn ->
    match extract output pass file warn with
    | () -> ()
    | exception HiError e ->
        Format.eprintf "%a@." pp_hierror e;
        exit 1

let output =
  let doc = "Output file. If not given, output will be printed on stdout." in
  Arg.(
    value
    & opt (some string) None
    & info [ "o"; "output" ] ~docv:"OUTPUT FILE" ~doc)

let after_pass =
  let alts =
    List.map
      (fun s -> (fst (Glob_options.print_strings s), s))
      Compiler.(List.filter (( > ) StackAllocation) compiler_step_list)
  in
  let doc =
    Format.asprintf "Run after the given compilation pass (%s)."
      (Arg.doc_alts_enum alts)
  in
  let passes = Arg.enum alts in
  Arg.(value & opt passes ParamsExpansion & info [ "compile"; "after" ] ~doc)

let file =
  let doc = "The Jasmin source file to extract" in
  Arg.(required & pos 0 (some non_dir_file) None & info [] ~docv:"JAZZ" ~doc)

(* TODO include slicing *)

let () =
  let doc = "Extract Jasmin program to Rocq representation" in
  let man =
    [
      `S Manpage.s_environment;
      Manpage.s_environment_intro;
      `I ("OCAMLRUNPARAM", "This is an OCaml program");
      `I ("JASMINPATH", "To resolve $(i,require) directives");
    ]
  in
  let info =
    Cmd.info "jasmin2rocq" ~version:Glob_options.version_string ~doc ~man
  in
  Cmd.v info
    Term.(
      const parse_and_extract $ arch $ call_conv $ idirs
      $ output $ after_pass $ file $ warn)
  |> Cmd.eval |> exit
