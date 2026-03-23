open Jasmin
open Cmdliner
open CommonCLI
open Utils

module F = Format

(* -------------------------------------------------------------------- *)
(* Architecture-specific asm_op printer for x86.
   Generic parts (pp_wsize, pp_velem, pp_option) live in ToRocq. *)

(* Helpers for printing constructors with their arguments *)
let pp_ws name fmt ws =
  F.fprintf fmt "(%s %a)" name ToRocq.pp_wsize ws

let pp_ws2 name fmt (ws1, ws2) =
  F.fprintf fmt "(%s %a %a)" name ToRocq.pp_wsize ws1 ToRocq.pp_wsize ws2

let pp_ve_ws name fmt (ve, ws) =
  F.fprintf fmt "(%s %a %a)" name ToRocq.pp_velem ve ToRocq.pp_wsize ws

let pp_ve_ws_ve_ws name fmt (ve1, ws1, ve2, ws2) =
  F.fprintf fmt "(%s %a %a %a %a)" name
    ToRocq.pp_velem ve1 ToRocq.pp_wsize ws1
    ToRocq.pp_velem ve2 ToRocq.pp_wsize ws2

let pp_ve name fmt ve =
  F.fprintf fmt "(%s %a)" name ToRocq.pp_velem ve

let pp_reg_kind fmt = function
  | Wsize.Normal -> F.fprintf fmt "Normal"
  | Wsize.Extra  -> F.fprintf fmt "Extra"

(* Single pp_base: wraps any inner op printer in BaseOp(msb, ...) *)
let pp_base fmt msb pp_inner =
  F.fprintf fmt "(BaseOp (%a, %t))"
    (ToRocq.pp_option ToRocq.pp_wsize) msb pp_inner

let pp_x86_op fmt (o : (_, _, _, _, _, X86_instr_decl.x86_op, X86_extra.x86_extra_op) Arch_extra.extended_op) =
  match o with
  (* BaseOp: x86_op with wsize *)
  | BaseOp (msb, MOV ws) -> pp_base fmt msb (fun fmt -> pp_ws "MOV" fmt ws)
  | BaseOp (msb, CMOVcc ws) -> pp_base fmt msb (fun fmt -> pp_ws "CMOVcc" fmt ws)
  | BaseOp (msb, XCHG ws) -> pp_base fmt msb (fun fmt -> pp_ws "XCHG" fmt ws)
  | BaseOp (msb, ADD ws) -> pp_base fmt msb (fun fmt -> pp_ws "ADD" fmt ws)
  | BaseOp (msb, SUB ws) -> pp_base fmt msb (fun fmt -> pp_ws "SUB" fmt ws)
  | BaseOp (msb, MUL ws) -> pp_base fmt msb (fun fmt -> pp_ws "MUL" fmt ws)
  | BaseOp (msb, IMUL ws) -> pp_base fmt msb (fun fmt -> pp_ws "IMUL" fmt ws)
  | BaseOp (msb, IMULr ws) -> pp_base fmt msb (fun fmt -> pp_ws "IMULr" fmt ws)
  | BaseOp (msb, IMULri ws) -> pp_base fmt msb (fun fmt -> pp_ws "IMULri" fmt ws)
  | BaseOp (msb, DIV ws) -> pp_base fmt msb (fun fmt -> pp_ws "DIV" fmt ws)
  | BaseOp (msb, IDIV ws) -> pp_base fmt msb (fun fmt -> pp_ws "IDIV" fmt ws)
  | BaseOp (msb, CQO ws) -> pp_base fmt msb (fun fmt -> pp_ws "CQO" fmt ws)
  | BaseOp (msb, ADC ws) -> pp_base fmt msb (fun fmt -> pp_ws "ADC" fmt ws)
  | BaseOp (msb, SBB ws) -> pp_base fmt msb (fun fmt -> pp_ws "SBB" fmt ws)
  | BaseOp (msb, NEG ws) -> pp_base fmt msb (fun fmt -> pp_ws "NEG" fmt ws)
  | BaseOp (msb, INC ws) -> pp_base fmt msb (fun fmt -> pp_ws "INC" fmt ws)
  | BaseOp (msb, DEC ws) -> pp_base fmt msb (fun fmt -> pp_ws "DEC" fmt ws)
  | BaseOp (msb, LZCNT ws) -> pp_base fmt msb (fun fmt -> pp_ws "LZCNT" fmt ws)
  | BaseOp (msb, TZCNT ws) -> pp_base fmt msb (fun fmt -> pp_ws "TZCNT" fmt ws)
  | BaseOp (msb, BSR ws) -> pp_base fmt msb (fun fmt -> pp_ws "BSR" fmt ws)
  | BaseOp (msb, BT ws) -> pp_base fmt msb (fun fmt -> pp_ws "BT" fmt ws)
  | BaseOp (msb, LEA ws) -> pp_base fmt msb (fun fmt -> pp_ws "LEA" fmt ws)
  | BaseOp (msb, TEST ws) -> pp_base fmt msb (fun fmt -> pp_ws "TEST" fmt ws)
  | BaseOp (msb, CMP ws) -> pp_base fmt msb (fun fmt -> pp_ws "CMP" fmt ws)
  | BaseOp (msb, AND ws) -> pp_base fmt msb (fun fmt -> pp_ws "AND" fmt ws)
  | BaseOp (msb, ANDN ws) -> pp_base fmt msb (fun fmt -> pp_ws "ANDN" fmt ws)
  | BaseOp (msb, OR ws) -> pp_base fmt msb (fun fmt -> pp_ws "OR" fmt ws)
  | BaseOp (msb, XOR ws) -> pp_base fmt msb (fun fmt -> pp_ws "XOR" fmt ws)
  | BaseOp (msb, NOT ws) -> pp_base fmt msb (fun fmt -> pp_ws "NOT" fmt ws)
  | BaseOp (msb, ROR ws) -> pp_base fmt msb (fun fmt -> pp_ws "ROR" fmt ws)
  | BaseOp (msb, ROL ws) -> pp_base fmt msb (fun fmt -> pp_ws "ROL" fmt ws)
  | BaseOp (msb, RCR ws) -> pp_base fmt msb (fun fmt -> pp_ws "RCR" fmt ws)
  | BaseOp (msb, RCL ws) -> pp_base fmt msb (fun fmt -> pp_ws "RCL" fmt ws)
  | BaseOp (msb, SHL ws) -> pp_base fmt msb (fun fmt -> pp_ws "SHL" fmt ws)
  | BaseOp (msb, SHR ws) -> pp_base fmt msb (fun fmt -> pp_ws "SHR" fmt ws)
  | BaseOp (msb, SAL ws) -> pp_base fmt msb (fun fmt -> pp_ws "SAL" fmt ws)
  | BaseOp (msb, SAR ws) -> pp_base fmt msb (fun fmt -> pp_ws "SAR" fmt ws)
  | BaseOp (msb, SHLD ws) -> pp_base fmt msb (fun fmt -> pp_ws "SHLD" fmt ws)
  | BaseOp (msb, SHRD ws) -> pp_base fmt msb (fun fmt -> pp_ws "SHRD" fmt ws)
  | BaseOp (msb, RORX ws) -> pp_base fmt msb (fun fmt -> pp_ws "RORX" fmt ws)
  | BaseOp (msb, SARX ws) -> pp_base fmt msb (fun fmt -> pp_ws "SARX" fmt ws)
  | BaseOp (msb, SHRX ws) -> pp_base fmt msb (fun fmt -> pp_ws "SHRX" fmt ws)
  | BaseOp (msb, SHLX ws) -> pp_base fmt msb (fun fmt -> pp_ws "SHLX" fmt ws)
  | BaseOp (msb, MULX_lo_hi ws) -> pp_base fmt msb (fun fmt -> pp_ws "MULX_lo_hi" fmt ws)
  | BaseOp (msb, ADCX ws) -> pp_base fmt msb (fun fmt -> pp_ws "ADCX" fmt ws)
  | BaseOp (msb, ADOX ws) -> pp_base fmt msb (fun fmt -> pp_ws "ADOX" fmt ws)
  | BaseOp (msb, BSWAP ws) -> pp_base fmt msb (fun fmt -> pp_ws "BSWAP" fmt ws)
  | BaseOp (msb, POPCNT ws) -> pp_base fmt msb (fun fmt -> pp_ws "POPCNT" fmt ws)
  | BaseOp (msb, BTR ws) -> pp_base fmt msb (fun fmt -> pp_ws "BTR" fmt ws)
  | BaseOp (msb, BTS ws) -> pp_base fmt msb (fun fmt -> pp_ws "BTS" fmt ws)
  | BaseOp (msb, PEXT ws) -> pp_base fmt msb (fun fmt -> pp_ws "PEXT" fmt ws)
  | BaseOp (msb, PDEP ws) -> pp_base fmt msb (fun fmt -> pp_ws "PDEP" fmt ws)
  | BaseOp (msb, MOVX ws) -> pp_base fmt msb (fun fmt -> pp_ws "MOVX" fmt ws)
  | BaseOp (msb, MOVD ws) -> pp_base fmt msb (fun fmt -> pp_ws "MOVD" fmt ws)
  | BaseOp (msb, MOVV ws) -> pp_base fmt msb (fun fmt -> pp_ws "MOVV" fmt ws)
  | BaseOp (msb, VMOV ws) -> pp_base fmt msb (fun fmt -> pp_ws "VMOV" fmt ws)
  | BaseOp (msb, VMOVDQA ws) -> pp_base fmt msb (fun fmt -> pp_ws "VMOVDQA" fmt ws)
  | BaseOp (msb, VMOVDQU ws) -> pp_base fmt msb (fun fmt -> pp_ws "VMOVDQU" fmt ws)
  | BaseOp (msb, VPAND ws) -> pp_base fmt msb (fun fmt -> pp_ws "VPAND" fmt ws)
  | BaseOp (msb, VPANDN ws) -> pp_base fmt msb (fun fmt -> pp_ws "VPANDN" fmt ws)
  | BaseOp (msb, VPOR ws) -> pp_base fmt msb (fun fmt -> pp_ws "VPOR" fmt ws)
  | BaseOp (msb, VPXOR ws) -> pp_base fmt msb (fun fmt -> pp_ws "VPXOR" fmt ws)
  | BaseOp (msb, VPMULH ws) -> pp_base fmt msb (fun fmt -> pp_ws "VPMULH" fmt ws)
  | BaseOp (msb, VPMULHU ws) -> pp_base fmt msb (fun fmt -> pp_ws "VPMULHU" fmt ws)
  | BaseOp (msb, VPMULHRS ws) -> pp_base fmt msb (fun fmt -> pp_ws "VPMULHRS" fmt ws)
  | BaseOp (msb, VPMUL ws) -> pp_base fmt msb (fun fmt -> pp_ws "VPMUL" fmt ws)
  | BaseOp (msb, VPMULU ws) -> pp_base fmt msb (fun fmt -> pp_ws "VPMULU" fmt ws)
  | BaseOp (msb, VPEXTR ws) -> pp_base fmt msb (fun fmt -> pp_ws "VPEXTR" fmt ws)
  | BaseOp (msb, VPSLLDQ ws) -> pp_base fmt msb (fun fmt -> pp_ws "VPSLLDQ" fmt ws)
  | BaseOp (msb, VPSRLDQ ws) -> pp_base fmt msb (fun fmt -> pp_ws "VPSRLDQ" fmt ws)
  | BaseOp (msb, VPSHUFB ws) -> pp_base fmt msb (fun fmt -> pp_ws "VPSHUFB" fmt ws)
  | BaseOp (msb, VPSHUFD ws) -> pp_base fmt msb (fun fmt -> pp_ws "VPSHUFD" fmt ws)
  | BaseOp (msb, VPSHUFHW ws) -> pp_base fmt msb (fun fmt -> pp_ws "VPSHUFHW" fmt ws)
  | BaseOp (msb, VPSHUFLW ws) -> pp_base fmt msb (fun fmt -> pp_ws "VPSHUFLW" fmt ws)
  | BaseOp (msb, VSHUFPS ws) -> pp_base fmt msb (fun fmt -> pp_ws "VSHUFPS" fmt ws)
  | BaseOp (msb, VMOVSHDUP ws) -> pp_base fmt msb (fun fmt -> pp_ws "VMOVSHDUP" fmt ws)
  | BaseOp (msb, VMOVSLDUP ws) -> pp_base fmt msb (fun fmt -> pp_ws "VMOVSLDUP" fmt ws)
  | BaseOp (msb, VPALIGNR ws) -> pp_base fmt msb (fun fmt -> pp_ws "VPALIGNR" fmt ws)
  | BaseOp (msb, VPTEST ws) -> pp_base fmt msb (fun fmt -> pp_ws "VPTEST" fmt ws)
  | BaseOp (msb, RDTSC ws) -> pp_base fmt msb (fun fmt -> pp_ws "RDTSC" fmt ws)
  | BaseOp (msb, RDTSCP ws) -> pp_base fmt msb (fun fmt -> pp_ws "RDTSCP" fmt ws)
  | BaseOp (msb, VAESDEC ws) -> pp_base fmt msb (fun fmt -> pp_ws "VAESDEC" fmt ws)
  | BaseOp (msb, VAESDECLAST ws) -> pp_base fmt msb (fun fmt -> pp_ws "VAESDECLAST" fmt ws)
  | BaseOp (msb, VAESENC ws) -> pp_base fmt msb (fun fmt -> pp_ws "VAESENC" fmt ws)
  | BaseOp (msb, VAESENCLAST ws) -> pp_base fmt msb (fun fmt -> pp_ws "VAESENCLAST" fmt ws)
  | BaseOp (msb, VPCLMULQDQ ws) -> pp_base fmt msb (fun fmt -> pp_ws "VPCLMULQDQ" fmt ws)
  | BaseOp (msb, VPMADDUBSW ws) -> pp_base fmt msb (fun fmt -> pp_ws "VPMADDUBSW" fmt ws)
  | BaseOp (msb, VPMADDWD ws) -> pp_base fmt msb (fun fmt -> pp_ws "VPMADDWD" fmt ws)
  (* BaseOp: x86_op with two wsizes *)
  | BaseOp (msb, MOVSX (w1, w2)) -> pp_base fmt msb (fun fmt -> pp_ws2 "MOVSX" fmt (w1, w2))
  | BaseOp (msb, MOVZX (w1, w2)) -> pp_base fmt msb (fun fmt -> pp_ws2 "MOVZX" fmt (w1, w2))
  (* BaseOp: x86_op with velem * wsize *)
  | BaseOp (msb, PADD (v, w)) -> pp_base fmt msb (fun fmt -> pp_ve_ws "PADD" fmt (v, w))
  | BaseOp (msb, VPADD (v, w)) -> pp_base fmt msb (fun fmt -> pp_ve_ws "VPADD" fmt (v, w))
  | BaseOp (msb, VPSUB (v, w)) -> pp_base fmt msb (fun fmt -> pp_ve_ws "VPSUB" fmt (v, w))
  | BaseOp (msb, VPAVG (v, w)) -> pp_base fmt msb (fun fmt -> pp_ve_ws "VPAVG" fmt (v, w))
  | BaseOp (msb, VPMULL (v, w)) -> pp_base fmt msb (fun fmt -> pp_ve_ws "VPMULL" fmt (v, w))
  | BaseOp (msb, VPSLL (v, w)) -> pp_base fmt msb (fun fmt -> pp_ve_ws "VPSLL" fmt (v, w))
  | BaseOp (msb, VPSRL (v, w)) -> pp_base fmt msb (fun fmt -> pp_ve_ws "VPSRL" fmt (v, w))
  | BaseOp (msb, VPSRA (v, w)) -> pp_base fmt msb (fun fmt -> pp_ve_ws "VPSRA" fmt (v, w))
  | BaseOp (msb, VPSLLV (v, w)) -> pp_base fmt msb (fun fmt -> pp_ve_ws "VPSLLV" fmt (v, w))
  | BaseOp (msb, VPSRLV (v, w)) -> pp_base fmt msb (fun fmt -> pp_ve_ws "VPSRLV" fmt (v, w))
  | BaseOp (msb, VPBLEND (v, w)) -> pp_base fmt msb (fun fmt -> pp_ve_ws "VPBLEND" fmt (v, w))
  | BaseOp (msb, BLENDV (v, w)) -> pp_base fmt msb (fun fmt -> pp_ve_ws "BLENDV" fmt (v, w))
  | BaseOp (msb, VPACKUS (v, w)) -> pp_base fmt msb (fun fmt -> pp_ve_ws "VPACKUS" fmt (v, w))
  | BaseOp (msb, VPACKSS (v, w)) -> pp_base fmt msb (fun fmt -> pp_ve_ws "VPACKSS" fmt (v, w))
  | BaseOp (msb, VPBROADCAST (v, w)) -> pp_base fmt msb (fun fmt -> pp_ve_ws "VPBROADCAST" fmt (v, w))
  | BaseOp (msb, VPUNPCKH (v, w)) -> pp_base fmt msb (fun fmt -> pp_ve_ws "VPUNPCKH" fmt (v, w))
  | BaseOp (msb, VPUNPCKL (v, w)) -> pp_base fmt msb (fun fmt -> pp_ve_ws "VPUNPCKL" fmt (v, w))
  | BaseOp (msb, MOVEMASK (v, w)) -> pp_base fmt msb (fun fmt -> pp_ve_ws "MOVEMASK" fmt (v, w))
  | BaseOp (msb, VPCMPEQ (v, w)) -> pp_base fmt msb (fun fmt -> pp_ve_ws "VPCMPEQ" fmt (v, w))
  | BaseOp (msb, VPCMPGT (v, w)) -> pp_base fmt msb (fun fmt -> pp_ve_ws "VPCMPGT" fmt (v, w))
  | BaseOp (msb, VPSIGN (v, w)) -> pp_base fmt msb (fun fmt -> pp_ve_ws "VPSIGN" fmt (v, w))
  | BaseOp (msb, VPMINU (v, w)) -> pp_base fmt msb (fun fmt -> pp_ve_ws "VPMINU" fmt (v, w))
  | BaseOp (msb, VPMINS (v, w)) -> pp_base fmt msb (fun fmt -> pp_ve_ws "VPMINS" fmt (v, w))
  | BaseOp (msb, VPMAXU (v, w)) -> pp_base fmt msb (fun fmt -> pp_ve_ws "VPMAXU" fmt (v, w))
  | BaseOp (msb, VPMAXS (v, w)) -> pp_base fmt msb (fun fmt -> pp_ve_ws "VPMAXS" fmt (v, w))
  | BaseOp (msb, VPABS (v, w)) -> pp_base fmt msb (fun fmt -> pp_ve_ws "VPABS" fmt (v, w))
  (* BaseOp: x86_op with velem * wsize * velem * wsize *)
  | BaseOp (msb, VPMOVSX (v1, w1, v2, w2)) -> pp_base fmt msb (fun fmt -> pp_ve_ws_ve_ws "VPMOVSX" fmt (v1, w1, v2, w2))
  | BaseOp (msb, VPMOVZX (v1, w1, v2, w2)) -> pp_base fmt msb (fun fmt -> pp_ve_ws_ve_ws "VPMOVZX" fmt (v1, w1, v2, w2))
  (* BaseOp: x86_op with velem only *)
  | BaseOp (msb, VPINSR ve) -> pp_base fmt msb (fun fmt -> pp_ve "VPINSR" fmt ve)
  (* BaseOp: x86_op with no arguments *)
  | BaseOp (msb, SETcc) -> pp_base fmt msb (fun fmt -> F.fprintf fmt "SETcc")
  | BaseOp (msb, CLC) -> pp_base fmt msb (fun fmt -> F.fprintf fmt "CLC")
  | BaseOp (msb, STC) -> pp_base fmt msb (fun fmt -> F.fprintf fmt "STC")
  | BaseOp (msb, POR) -> pp_base fmt msb (fun fmt -> F.fprintf fmt "POR")
  | BaseOp (msb, VBROADCASTI128) -> pp_base fmt msb (fun fmt -> F.fprintf fmt "VBROADCASTI128")
  | BaseOp (msb, VEXTRACTI128) -> pp_base fmt msb (fun fmt -> F.fprintf fmt "VEXTRACTI128")
  | BaseOp (msb, VINSERTI128) -> pp_base fmt msb (fun fmt -> F.fprintf fmt "VINSERTI128")
  | BaseOp (msb, VPERM2I128) -> pp_base fmt msb (fun fmt -> F.fprintf fmt "VPERM2I128")
  | BaseOp (msb, VPERMD) -> pp_base fmt msb (fun fmt -> F.fprintf fmt "VPERMD")
  | BaseOp (msb, VPERMQ) -> pp_base fmt msb (fun fmt -> F.fprintf fmt "VPERMQ")
  | BaseOp (msb, VMOVLPD) -> pp_base fmt msb (fun fmt -> F.fprintf fmt "VMOVLPD")
  | BaseOp (msb, VMOVHPD) -> pp_base fmt msb (fun fmt -> F.fprintf fmt "VMOVHPD")
  | BaseOp (msb, CLFLUSH) -> pp_base fmt msb (fun fmt -> F.fprintf fmt "CLFLUSH")
  | BaseOp (msb, PREFETCHT0) -> pp_base fmt msb (fun fmt -> F.fprintf fmt "PREFETCHT0")
  | BaseOp (msb, PREFETCHT1) -> pp_base fmt msb (fun fmt -> F.fprintf fmt "PREFETCHT1")
  | BaseOp (msb, PREFETCHT2) -> pp_base fmt msb (fun fmt -> F.fprintf fmt "PREFETCHT2")
  | BaseOp (msb, PREFETCHNTA) -> pp_base fmt msb (fun fmt -> F.fprintf fmt "PREFETCHNTA")
  | BaseOp (msb, LFENCE) -> pp_base fmt msb (fun fmt -> F.fprintf fmt "LFENCE")
  | BaseOp (msb, MFENCE) -> pp_base fmt msb (fun fmt -> F.fprintf fmt "MFENCE")
  | BaseOp (msb, SFENCE) -> pp_base fmt msb (fun fmt -> F.fprintf fmt "SFENCE")
  | BaseOp (msb, AESDEC) -> pp_base fmt msb (fun fmt -> F.fprintf fmt "AESDEC")
  | BaseOp (msb, AESDECLAST) -> pp_base fmt msb (fun fmt -> F.fprintf fmt "AESDECLAST")
  | BaseOp (msb, AESENC) -> pp_base fmt msb (fun fmt -> F.fprintf fmt "AESENC")
  | BaseOp (msb, AESENCLAST) -> pp_base fmt msb (fun fmt -> F.fprintf fmt "AESENCLAST")
  | BaseOp (msb, AESIMC) -> pp_base fmt msb (fun fmt -> F.fprintf fmt "AESIMC")
  | BaseOp (msb, VAESIMC) -> pp_base fmt msb (fun fmt -> F.fprintf fmt "VAESIMC")
  | BaseOp (msb, AESKEYGENASSIST) -> pp_base fmt msb (fun fmt -> F.fprintf fmt "AESKEYGENASSIST")
  | BaseOp (msb, VAESKEYGENASSIST) -> pp_base fmt msb (fun fmt -> F.fprintf fmt "VAESKEYGENASSIST")
  | BaseOp (msb, PCLMULQDQ) -> pp_base fmt msb (fun fmt -> F.fprintf fmt "PCLMULQDQ")
  | BaseOp (msb, SHA256RNDS2) -> pp_base fmt msb (fun fmt -> F.fprintf fmt "SHA256RNDS2")
  | BaseOp (msb, SHA256MSG1) -> pp_base fmt msb (fun fmt -> F.fprintf fmt "SHA256MSG1")
  | BaseOp (msb, SHA256MSG2) -> pp_base fmt msb (fun fmt -> F.fprintf fmt "SHA256MSG2")
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
    F.fprintf fmt "(ExtOp (Ox86SLHprotect %a %a))" pp_reg_kind rk ToRocq.pp_wsize ws

(* -------------------------------------------------------------------- *)

let parse_and_extract arch call_conv idirs =
  let module A = (val CoreArchFactory.get_arch_module arch call_conv) in
  let extract output pass file warn =
    if not warn then nowarning ();
    let prog =
      parse_and_compile (module A) ~wi2i:false pass file idirs
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
         (Obj.magic pp_x86_op) fmt;
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
