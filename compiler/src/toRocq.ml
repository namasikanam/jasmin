open Utils
open Prog
open Wsize
open Operators

module F = Format
module SS = Set.Make(String)

(* -------------------------------------------------------------------- *)
(* Name sanitization: turn Jasmin names into valid Rocq identifiers.
   Jasmin names may contain '.', '#', and other non-alphanumeric characters
   (e.g. after inlining: "f.x.42", after SSA: "x#3"). *)

let sanitize_char c =
  if (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z')
     || (c >= '0' && c <= '9') || c = '_' then c
  else '_'

let sanitize_name prefix s =
  let buf = Buffer.create (String.length prefix + String.length s) in
  Buffer.add_string buf prefix;
  String.iter (fun c -> Buffer.add_char buf (sanitize_char c)) s;
  Buffer.contents buf

(* -------------------------------------------------------------------- *)
(* Name collection: gather all variable and function names in a program *)

let collect_prog_names ((gd, funcs) : (unit, _) prog) =
  let vars =
    List.fold_left (fun acc fd ->
      Sv.fold (fun v acc -> SS.add v.v_name acc) (vars_fc fd) acc
    ) SS.empty funcs
  in
  let vars =
    List.fold_left (fun acc (x, _) -> SS.add x.v_name acc) vars gd
  in
  let funs =
    List.fold_left (fun acc fd ->
      let acc = SS.add fd.f_name.fn_name acc in
      Sv.fold (fun _ acc -> acc) (vars_fc fd) acc |> ignore;
      (* Collect funnames from Ccall sites *)
      let rec from_stmt acc c = List.fold_left from_instr acc c
      and from_instr acc i =
        match i.i_desc with
        | Ccall (_, fn, _) -> SS.add fn.fn_name acc
        | Cif (_, c1, c2) -> from_stmt (from_stmt acc c1) c2
        | Cfor (_, _, c) -> from_stmt acc c
        | Cwhile (_, c1, _, _, c2) -> from_stmt (from_stmt acc c1) c2
        | _ -> acc
      in
      from_stmt acc fd.f_body
    ) SS.empty funcs
  in
  (vars, funs)

(* -------------------------------------------------------------------- *)
(* Helpers *)

let pp_list _sep pp fmt = function
  | [] -> F.fprintf fmt "[::]"
  | xs ->
    F.fprintf fmt "[:: @[<hov>%a@]]"
      (Utils.pp_list ";@ " pp) xs

let pp_option pp fmt = function
  | None -> F.fprintf fmt "None"
  | Some x -> F.fprintf fmt "(Some %a)" pp x

let pp_string fmt s =
  F.fprintf fmt "%S" s

let pp_z fmt z =
  let s = Z.to_string z in
  if Z.leq Z.zero z then
    F.fprintf fmt "%s%%Z" s
  else
    F.fprintf fmt "(%s)%%Z" s

let pp_positive fmt p =
  F.fprintf fmt "%s%%positive" (Z.to_string (Conv.z_of_pos p))

(* -------------------------------------------------------------------- *)
(* Wsize *)

let pp_wsize fmt = function
  | U8   -> F.fprintf fmt "U8"
  | U16  -> F.fprintf fmt "U16"
  | U32  -> F.fprintf fmt "U32"
  | U64  -> F.fprintf fmt "U64"
  | U128 -> F.fprintf fmt "U128"
  | U256 -> F.fprintf fmt "U256"

(* -------------------------------------------------------------------- *)
(* Signedness *)

let pp_signedness fmt = function
  | Signed   -> F.fprintf fmt "Signed"
  | Unsigned -> F.fprintf fmt "Unsigned"

(* -------------------------------------------------------------------- *)
(* Types *)

let pp_atype fmt = function
  | Bty Bool  -> F.fprintf fmt "abool"
  | Bty Int   -> F.fprintf fmt "aint"
  | Bty (U ws) -> F.fprintf fmt "(aword %a)" pp_wsize ws
  | Arr (ws, n) -> F.fprintf fmt "(aarr %a %d)" pp_wsize ws n

(* -------------------------------------------------------------------- *)
(* Aligned *)

let pp_aligned fmt = function
  | Memory_model.Aligned   -> F.fprintf fmt "Aligned"
  | Memory_model.Unaligned -> F.fprintf fmt "Unaligned"

(* -------------------------------------------------------------------- *)
(* Array access *)

let pp_arr_access fmt = function
  | Warray_.AAscale  -> F.fprintf fmt "AAscale"
  | Warray_.AAdirect -> F.fprintf fmt "AAdirect"

(* -------------------------------------------------------------------- *)
(* Assgn tag *)

let pp_assgn_tag fmt = function
  | Expr.AT_none    -> F.fprintf fmt "AT_none"
  | Expr.AT_keep    -> F.fprintf fmt "AT_keep"
  | Expr.AT_rename  -> F.fprintf fmt "AT_rename"
  | Expr.AT_inline  -> F.fprintf fmt "AT_inline"
  | Expr.AT_phinode -> F.fprintf fmt "AT_phinode"

(* -------------------------------------------------------------------- *)
(* Align *)

let pp_align fmt = function
  | Expr.Align   -> F.fprintf fmt "Align"
  | Expr.NoAlign -> F.fprintf fmt "NoAlign"

(* -------------------------------------------------------------------- *)
(* Direction *)

let pp_dir fmt = function
  | Expr.UpTo   -> F.fprintf fmt "UpTo"
  | Expr.DownTo -> F.fprintf fmt "DownTo"

(* -------------------------------------------------------------------- *)
(* Variables - use sanitized identifiers.
   The v_ prefix avoids clashing with Rocq keywords and constructor names. *)

let pp_var fmt (x : var) =
  F.fprintf fmt "%s" (sanitize_name "v_" x.v_name)

let pp_var_i fmt (x : var_i) =
  let v = L.unloc x in
  F.fprintf fmt "%s" (sanitize_name "v_" v.v_name)

(* -------------------------------------------------------------------- *)
(* Gvar *)

let pp_gvar fmt (x : int ggvar) =
  let name = sanitize_name "v_" (L.unloc x.gv).v_name in
  match x.gs with
  | Expr.Slocal -> F.fprintf fmt "(mk_lvar %s)" name
  | Expr.Sglob  -> F.fprintf fmt "(mk_gvar %s)" name

(* -------------------------------------------------------------------- *)
(* Op_kind *)

let pp_op_kind fmt = function
  | Op_int  -> F.fprintf fmt "Op_int"
  | Op_w ws -> F.fprintf fmt "(Op_w %a)" pp_wsize ws

(* -------------------------------------------------------------------- *)
(* Cmp_kind *)

let pp_cmp_kind fmt = function
  | Cmp_int -> F.fprintf fmt "Cmp_int"
  | Cmp_w (s, ws) -> F.fprintf fmt "(Cmp_w %a %a)" pp_signedness s pp_wsize ws

(* -------------------------------------------------------------------- *)
(* Velem / pelem *)

let pp_pelem fmt = function
  | PE1   -> F.fprintf fmt "PE1"
  | PE2   -> F.fprintf fmt "PE2"
  | PE4   -> F.fprintf fmt "PE4"
  | PE8   -> F.fprintf fmt "PE8"
  | PE16  -> F.fprintf fmt "PE16"
  | PE32  -> F.fprintf fmt "PE32"
  | PE64  -> F.fprintf fmt "PE64"
  | PE128 -> F.fprintf fmt "PE128"

let pp_velem fmt = function
  | VE8  -> F.fprintf fmt "VE8"
  | VE16 -> F.fprintf fmt "VE16"
  | VE32 -> F.fprintf fmt "VE32"
  | VE64 -> F.fprintf fmt "VE64"

(* -------------------------------------------------------------------- *)
(* Unary operators *)

let pp_wiop1 fmt = function
  | WIwint_of_int ws  -> F.fprintf fmt "(WIwint_of_int %a)" pp_wsize ws
  | WIint_of_wint ws  -> F.fprintf fmt "(WIint_of_wint %a)" pp_wsize ws
  | WIword_of_wint ws -> F.fprintf fmt "(WIword_of_wint %a)" pp_wsize ws
  | WIwint_of_word ws -> F.fprintf fmt "(WIwint_of_word %a)" pp_wsize ws
  | WIwint_ext (szo, szi) -> F.fprintf fmt "(WIwint_ext %a %a)" pp_wsize szo pp_wsize szi
  | WIneg ws          -> F.fprintf fmt "(WIneg %a)" pp_wsize ws

let pp_sop1 fmt = function
  | Oword_of_int ws    -> F.fprintf fmt "(Oword_of_int %a)" pp_wsize ws
  | Oint_of_word (s,ws) -> F.fprintf fmt "(Oint_of_word %a %a)" pp_signedness s pp_wsize ws
  | Osignext (szo, szi) -> F.fprintf fmt "(Osignext %a %a)" pp_wsize szo pp_wsize szi
  | Ozeroext (szo, szi) -> F.fprintf fmt "(Ozeroext %a %a)" pp_wsize szo pp_wsize szi
  | Onot                -> F.fprintf fmt "Onot"
  | Olnot ws           -> F.fprintf fmt "(Olnot %a)" pp_wsize ws
  | Oneg k             -> F.fprintf fmt "(Oneg %a)" pp_op_kind k
  | Owi1 (sg, o)       -> F.fprintf fmt "(Owi1 %a %a)" pp_signedness sg pp_wiop1 o

(* -------------------------------------------------------------------- *)
(* Binary operators *)

let pp_wiop2 fmt = function
  | WIadd -> F.fprintf fmt "WIadd"
  | WImul -> F.fprintf fmt "WImul"
  | WIsub -> F.fprintf fmt "WIsub"
  | WIdiv -> F.fprintf fmt "WIdiv"
  | WImod -> F.fprintf fmt "WImod"
  | WIshl -> F.fprintf fmt "WIshl"
  | WIshr -> F.fprintf fmt "WIshr"
  | WIeq  -> F.fprintf fmt "WIeq"
  | WIneq -> F.fprintf fmt "WIneq"
  | WIlt  -> F.fprintf fmt "WIlt"
  | WIle  -> F.fprintf fmt "WIle"
  | WIgt  -> F.fprintf fmt "WIgt"
  | WIge  -> F.fprintf fmt "WIge"

let pp_sop2 fmt = function
  | Obeq    -> F.fprintf fmt "Obeq"
  | Oand    -> F.fprintf fmt "Oand"
  | Oor     -> F.fprintf fmt "Oor"
  | Oadd k  -> F.fprintf fmt "(Oadd %a)" pp_op_kind k
  | Omul k  -> F.fprintf fmt "(Omul %a)" pp_op_kind k
  | Osub k  -> F.fprintf fmt "(Osub %a)" pp_op_kind k
  | Odiv (s, k) -> F.fprintf fmt "(Odiv %a %a)" pp_signedness s pp_op_kind k
  | Omod (s, k) -> F.fprintf fmt "(Omod %a %a)" pp_signedness s pp_op_kind k
  | Oland ws -> F.fprintf fmt "(Oland %a)" pp_wsize ws
  | Olor ws  -> F.fprintf fmt "(Olor %a)" pp_wsize ws
  | Olxor ws -> F.fprintf fmt "(Olxor %a)" pp_wsize ws
  | Olsr ws  -> F.fprintf fmt "(Olsr %a)" pp_wsize ws
  | Olsl k   -> F.fprintf fmt "(Olsl %a)" pp_op_kind k
  | Oasr k   -> F.fprintf fmt "(Oasr %a)" pp_op_kind k
  | Oror ws  -> F.fprintf fmt "(Oror %a)" pp_wsize ws
  | Orol ws  -> F.fprintf fmt "(Orol %a)" pp_wsize ws
  | Oeq k    -> F.fprintf fmt "(Oeq %a)" pp_op_kind k
  | Oneq k   -> F.fprintf fmt "(Oneq %a)" pp_op_kind k
  | Olt k    -> F.fprintf fmt "(Olt %a)" pp_cmp_kind k
  | Ole k    -> F.fprintf fmt "(Ole %a)" pp_cmp_kind k
  | Ogt k    -> F.fprintf fmt "(Ogt %a)" pp_cmp_kind k
  | Oge k    -> F.fprintf fmt "(Oge %a)" pp_cmp_kind k
  | Ovadd (ve, ws) -> F.fprintf fmt "(Ovadd %a %a)" pp_velem ve pp_wsize ws
  | Ovsub (ve, ws) -> F.fprintf fmt "(Ovsub %a %a)" pp_velem ve pp_wsize ws
  | Ovmul (ve, ws) -> F.fprintf fmt "(Ovmul %a %a)" pp_velem ve pp_wsize ws
  | Ovlsr (ve, ws) -> F.fprintf fmt "(Ovlsr %a %a)" pp_velem ve pp_wsize ws
  | Ovlsl (ve, ws) -> F.fprintf fmt "(Ovlsl %a %a)" pp_velem ve pp_wsize ws
  | Ovasr (ve, ws) -> F.fprintf fmt "(Ovasr %a %a)" pp_velem ve pp_wsize ws
  | Owi2 (sg, ws, o) -> F.fprintf fmt "(Owi2 %a %a %a)" pp_signedness sg pp_wsize ws pp_wiop2 o

(* -------------------------------------------------------------------- *)
(* N-ary operators *)

let pp_combine_flags fmt = function
  | CF_LT s -> F.fprintf fmt "(CF_LT %a)" pp_signedness s
  | CF_LE s -> F.fprintf fmt "(CF_LE %a)" pp_signedness s
  | CF_EQ   -> F.fprintf fmt "CF_EQ"
  | CF_NEQ  -> F.fprintf fmt "CF_NEQ"
  | CF_GE s -> F.fprintf fmt "(CF_GE %a)" pp_signedness s
  | CF_GT s -> F.fprintf fmt "(CF_GT %a)" pp_signedness s

let pp_opN fmt = function
  | Opack (ws, pe) -> F.fprintf fmt "(Opack %a %a)" pp_wsize ws pp_pelem pe
  | Oarray len     -> F.fprintf fmt "(Oarray %a)" pp_positive len
  | Ocombine_flags c -> F.fprintf fmt "(Ocombine_flags %a)" pp_combine_flags c

let pp_opN_safety fmt = function
  | Ois_arr_init len  -> F.fprintf fmt "(Ois_arr_init %a)" pp_positive len
  | Ois_barr_init len -> F.fprintf fmt "(Ois_barr_init %a)" pp_positive len

(* -------------------------------------------------------------------- *)
(* Sopn *)

let pp_spill_op fmt = function
  | Pseudo_operator.Spill   -> F.fprintf fmt "Spill"
  | Pseudo_operator.Unspill -> F.fprintf fmt "Unspill"

let pp_cil_atype fmt = function
  | Type.Coq_abool -> F.fprintf fmt "abool"
  | Type.Coq_aint  -> F.fprintf fmt "aint"
  | Type.Coq_aword ws -> F.fprintf fmt "(aword %a)" pp_wsize ws
  | Type.Coq_aarr (ws, p) -> F.fprintf fmt "(aarr %a %a)" pp_wsize ws pp_positive p

let pp_pseudo_operator fmt = function
  | Pseudo_operator.Ospill (o, tys) ->
    F.fprintf fmt "(Ospill %a %a)" pp_spill_op o (pp_list "" pp_cil_atype) tys
  | Pseudo_operator.Ocopy (ws, p) ->
    F.fprintf fmt "(Ocopy %a %a)" pp_wsize ws pp_positive p
  | Pseudo_operator.Odeclassify ty ->
    F.fprintf fmt "(Odeclassify %a)" pp_cil_atype ty
  | Pseudo_operator.Odeclassify_mem p ->
    F.fprintf fmt "(Odeclassify_mem %a)" pp_positive p
  | Pseudo_operator.Onop -> F.fprintf fmt "Onop"
  | Pseudo_operator.Omulu ws ->
    F.fprintf fmt "(Omulu %a)" pp_wsize ws
  | Pseudo_operator.Oaddcarry ws ->
    F.fprintf fmt "(Oaddcarry %a)" pp_wsize ws
  | Pseudo_operator.Osubcarry ws ->
    F.fprintf fmt "(Osubcarry %a)" pp_wsize ws
  | Pseudo_operator.Oswap ty ->
    F.fprintf fmt "(Oswap %a)" pp_cil_atype ty

let pp_slh_op fmt = function
  | Slh_ops.SLHinit -> F.fprintf fmt "SLHinit"
  | Slh_ops.SLHupdate -> F.fprintf fmt "SLHupdate"
  | Slh_ops.SLHmove -> F.fprintf fmt "SLHmove"
  | Slh_ops.SLHprotect ws ->
    F.fprintf fmt "(SLHprotect %a)" pp_wsize ws
  | Slh_ops.SLHprotect_ptr (ws, p) ->
    F.fprintf fmt "(SLHprotect_ptr %a %a)" pp_wsize ws pp_positive p
  | Slh_ops.SLHprotect_ptr_fail (ws, p) ->
    F.fprintf fmt "(SLHprotect_ptr_fail %a %a)" pp_wsize ws pp_positive p

let pp_sopn pp_asm_op fmt = function
  | Sopn.Opseudo_op o ->
    F.fprintf fmt "(Opseudo_op %a)" pp_pseudo_operator o
  | Sopn.Oslh o ->
    F.fprintf fmt "(Oslh %a)" pp_slh_op o
  | Sopn.Oasm o ->
    F.fprintf fmt "(Oasm %a)" pp_asm_op o

(* -------------------------------------------------------------------- *)
(* Syscall *)

let pp_syscall fmt (o : _ Syscall_t.syscall_t) =
  match o with
  | Syscall_t.RandomBytes (ws, n) ->
    F.fprintf fmt "(RandomBytes (%a, %a))" pp_wsize ws pp_positive n

(* -------------------------------------------------------------------- *)
(* Expressions *)

let rec pp_expr fmt = function
  | Pconst z ->
    F.fprintf fmt "(Pconst %a)" pp_z z

  | Pbool b ->
    F.fprintf fmt "(Pbool %b)" b

  | Parr_init (ws, n) ->
    F.fprintf fmt "(Parr_init %a %d)" pp_wsize ws n

  | Pvar gv ->
    F.fprintf fmt "(Pvar %a)" pp_gvar gv

  | Pget (al, aa, ws, gv, e) ->
    F.fprintf fmt "@[<hov 2>(Pget %a %a %a@ %a@ %a)@]"
      pp_aligned al pp_arr_access aa pp_wsize ws pp_gvar gv pp_expr e

  | Psub (aa, ws, len, gv, e) ->
    F.fprintf fmt "@[<hov 2>(Psub %a %a %d@ %a@ %a)@]"
      pp_arr_access aa pp_wsize ws len pp_gvar gv pp_expr e

  | Pload (al, ws, e) ->
    F.fprintf fmt "@[<hov 2>(Pload %a %a@ %a)@]"
      pp_aligned al pp_wsize ws pp_expr e

  | Papp1 (op, e) ->
    F.fprintf fmt "@[<hov 2>(Papp1 %a@ %a)@]"
      pp_sop1 op pp_expr e

  | Papp2 (op, e1, e2) ->
    F.fprintf fmt "@[<hov 2>(Papp2 %a@ %a@ %a)@]"
      pp_sop2 op pp_expr e1 pp_expr e2

  | PappN (op, es) ->
    F.fprintf fmt "@[<hov 2>(PappN %a@ %a)@]"
      pp_opN op (pp_list "" pp_expr) es

  | Pif (ty, e1, e2, e3) ->
    F.fprintf fmt "@[<hov 2>(Pif %a@ %a@ %a@ %a)@]"
      pp_atype ty pp_expr e1 pp_expr e2 pp_expr e3

let pp_exprs fmt es = pp_list "" pp_expr fmt es

(* -------------------------------------------------------------------- *)
(* Assertions *)

let rec pp_eassert fmt = function
  | Pexpr e ->
    F.fprintf fmt "(Pexpr %a)" pp_expr e

  | PappN_safety (op, es) ->
    F.fprintf fmt "@[<hov 2>(PappN_safety %a@ %a)@]"
      pp_opN_safety op (pp_list "" pp_expr) es

  | Pis_var_init x ->
    F.fprintf fmt "(Pis_var_init %a)" pp_var_i x

  | Pis_mem_init (e1, e2) ->
    F.fprintf fmt "@[<hov 2>(Pis_mem_init %a@ %a)@]"
      pp_expr e1 pp_expr e2

  | Pand (a1, a2) ->
    F.fprintf fmt "@[<hov 2>(Pand %a@ %a)@]"
      pp_eassert a1 pp_eassert a2

let pp_assertion fmt (label, a) =
  F.fprintf fmt "(%S, %a)" label pp_eassert a

(* -------------------------------------------------------------------- *)
(* Lvals *)

let pp_lval fmt = function
  | Lnone (_, ty) ->
    F.fprintf fmt "(Lnone dummy_var_info %a)" pp_atype ty

  | Lvar x ->
    F.fprintf fmt "(Lvar %a)" pp_var_i x

  | Lmem (al, ws, _, e) ->
    F.fprintf fmt "@[<hov 2>(Lmem %a %a dummy_var_info@ %a)@]"
      pp_aligned al pp_wsize ws pp_expr e

  | Laset (al, aa, ws, x, e) ->
    F.fprintf fmt "@[<hov 2>(Laset %a %a %a@ %a@ %a)@]"
      pp_aligned al pp_arr_access aa pp_wsize ws pp_var_i x pp_expr e

  | Lasub (aa, ws, len, x, e) ->
    F.fprintf fmt "@[<hov 2>(Lasub %a %a %d@ %a@ %a)@]"
      pp_arr_access aa pp_wsize ws len pp_var_i x pp_expr e

let pp_lvals fmt lvs = pp_list "" pp_lval fmt lvs

(* -------------------------------------------------------------------- *)
(* Instructions *)

let rec pp_instr_r pp_asm_op fmt = function
  | Cassgn (lv, tag, ty, e) ->
    F.fprintf fmt "@[<hov 2>(Cassgn %a@ %a %a@ %a)@]"
      pp_lval lv pp_assgn_tag tag pp_atype ty pp_expr e

  | Copn (lvs, tag, op, es) ->
    F.fprintf fmt "@[<hov 2>(Copn %a@ %a %a@ %a)@]"
      pp_lvals lvs pp_assgn_tag tag (pp_sopn pp_asm_op) op pp_exprs es

  | Csyscall (lvs, sc, es) ->
    F.fprintf fmt "@[<hov 2>(Csyscall %a@ %a@ %a)@]"
      pp_lvals lvs pp_syscall sc pp_exprs es

  | Cassert (label, a) ->
    F.fprintf fmt "@[<hov 2>(Cassert %a)@]"
      pp_assertion (label, a)

  | Cif (e, c1, c2) ->
    F.fprintf fmt "@[<v 2>(Cif %a@ %a@ %a)@]"
      pp_expr e (pp_stmt pp_asm_op) c1 (pp_stmt pp_asm_op) c2

  | Cfor (x, (dir, lo, hi), c) ->
    F.fprintf fmt "@[<v 2>(Cfor %a (%a, %a, %a)@ %a)@]"
      pp_var_i x pp_dir dir pp_expr lo pp_expr hi
      (pp_stmt pp_asm_op) c

  | Cwhile (al, c1, e, _, c2) ->
    F.fprintf fmt "@[<v 2>(Cwhile %a@ %a@ %a@ dummy_instr_info@ %a)@]"
      pp_align al
      (pp_stmt pp_asm_op) c1
      pp_expr e
      (pp_stmt pp_asm_op) c2

  | Ccall (lvs, fn, es) ->
    F.fprintf fmt "@[<hov 2>(Ccall %a@ %s@ %a)@]"
      pp_lvals lvs (sanitize_name "fn_" fn.fn_name) pp_exprs es

and pp_instr pp_asm_op fmt i =
  F.fprintf fmt "@[<hov 2>(MkI dummy_instr_info@ %a)@]"
    (pp_instr_r pp_asm_op) i.i_desc

and pp_stmt pp_asm_op fmt c =
  pp_list "" (pp_instr pp_asm_op) fmt c

(* -------------------------------------------------------------------- *)
(* Functions *)

let pp_fun pp_asm_op fmt fd =
  F.fprintf fmt "@[<v 2>{|@ ";
  F.fprintf fmt "f_info := FunInfo.witness;@ ";
  F.fprintf fmt "f_contract := None;@ ";
  F.fprintf fmt "f_tyin := %a;@ " (pp_list "" pp_atype) fd.f_tyin;
  F.fprintf fmt "f_params := %a;@ "
    (pp_list "" pp_var) fd.f_args;
  F.fprintf fmt "f_body :=@ @[<v 0>%a@];@ " (pp_stmt pp_asm_op) fd.f_body;
  F.fprintf fmt "f_tyout := %a;@ " (pp_list "" pp_atype) fd.f_tyout;
  F.fprintf fmt "f_res := %a;@ " (pp_list "" pp_var_i) fd.f_ret;
  F.fprintf fmt "f_extra := tt;@ ";
  F.fprintf fmt "@]|}"

let pp_fun_decl pp_asm_op fmt fd =
  F.fprintf fmt "(%s,@ %a)"
    (sanitize_name "fn_" fd.f_name.fn_name)
    (pp_fun pp_asm_op) fd

(* -------------------------------------------------------------------- *)
(* Globals *)

let pp_glob_value fmt (x, gd) =
  match gd with
  | Global.Gword (ws, w) ->
    F.fprintf fmt "(%a : var, @Gword %a (wrepr %a %a))"
      pp_var x pp_wsize ws pp_wsize ws pp_z (Conv.z_of_word ws w)
  | Global.Garr (p, t) ->
    let ws, arr = Conv.to_array x.v_ty p t in
    let ws_bytes = int_of_ws ws / 8 in
    let n = Array.length arr in
    let total_bytes = n * ws_bytes in
    (* Extract individual bytes from each word in little-endian order *)
    let bytes = Array.make total_bytes Z.zero in
    Array.iteri (fun i w ->
      for b = 0 to ws_bytes - 1 do
        let byte_val = Z.logand (Z.shift_right w (b * 8)) (Z.of_int 255) in
        bytes.(i * ws_bytes + b) <- byte_val
      done
    ) arr;
    (* Print as nested Mz.set calls *)
    F.fprintf fmt "@[<hov 2>(%a : var,@ (@Garr %a@ {| WArray.arr_data :=@ "
      pp_var x pp_positive p;
    Array.iter (fun _byte_val ->
      F.fprintf fmt "(Mz.set@ "
    ) bytes;
    F.fprintf fmt "(Mz.empty u8)";
    Array.iteri (fun i byte_val ->
      F.fprintf fmt "@ %a@ (wrepr U8 %a))"
        pp_z (Z.of_int i) pp_z byte_val
    ) bytes;
    F.fprintf fmt "@ |}))@]"

(* -------------------------------------------------------------------- *)
(* Definition bindings *)

let pp_definitions fmt (vars, funs) =
  SS.iter (fun name ->
    F.fprintf fmt "Definition %s := mkvar %S.@ "
      (sanitize_name "v_" name) name
  ) vars;
  SS.iter (fun name ->
    F.fprintf fmt "Definition %s := mkfun %S.@ "
      (sanitize_name "fn_" name) name
  ) funs;
  F.fprintf fmt "@ "

(* -------------------------------------------------------------------- *)
(* Imports *)

let pp_imports fmt =
  F.fprintf fmt "From mathcomp Require Import ssreflect ssrfun ssrbool.@ ";
  F.fprintf fmt "From Coq Require Import ZArith.@ ";
  F.fprintf fmt "Require Import expr ident var type global warray_ pseudo_operator sopn arch_extra.@ ";
  F.fprintf fmt "Require Import x86_decl x86_instr_decl x86_extra.@ ";
  F.fprintf fmt "Import Utf8.@ @ ";
  F.fprintf fmt "Axiom mkvar : string -> var_i.@ ";
  F.fprintf fmt "Axiom mkfun : string -> funname.@ ";
  F.fprintf fmt "Axiom atoI : arch_toIdent.@ ";
  F.fprintf fmt "#[local] Existing Instance atoI.@ @ "

(* -------------------------------------------------------------------- *)
(* Program *)

let pp_prog ~split pp_asm_op fmt ((gd, funcs) : (unit, _) prog) =
  let names = collect_prog_names (gd, funcs) in
  let funcs_rev = List.rev funcs in
  F.fprintf fmt "@[<v 0>";
  pp_definitions fmt names;
  if split then begin
    (* Print each function as a separate Definition *)
    List.iter (fun fd ->
      F.fprintf fmt "Definition %s :=@ %a.@ @ "
        (sanitize_name "fd_" fd.f_name.fn_name)
        (pp_fun pp_asm_op) fd
    ) funcs_rev;
    F.fprintf fmt "Definition program :=@ ";
    F.fprintf fmt "@[<v 0>{|@ ";
    F.fprintf fmt "  p_funcs := %a;@ "
      (pp_list "" (fun fmt fd ->
        F.fprintf fmt "(%s, %s)"
          (sanitize_name "fn_" fd.f_name.fn_name)
          (sanitize_name "fd_" fd.f_name.fn_name)
      )) funcs_rev
  end else begin
    F.fprintf fmt "Definition program :=@ ";
    F.fprintf fmt "@[<v 0>{|@ ";
    F.fprintf fmt "  p_funcs := %a;@ "
      (pp_list "" (pp_fun_decl pp_asm_op)) funcs_rev
  end;
  F.fprintf fmt "  p_globs := %a;@ "
    (pp_list "" pp_glob_value) gd;
  F.fprintf fmt "  p_extra := tt;@ ";
  F.fprintf fmt "|}.@]@]@."

(* -------------------------------------------------------------------- *)
(* Entry point *)

let extract ~imports ~split prog _arch _pd _msfsz _asmOp pp_asm_op fmt =
  if imports then
    F.fprintf fmt "@[<v 0>%t@]" pp_imports;
  pp_prog ~split pp_asm_op fmt prog
