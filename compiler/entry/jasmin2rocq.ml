open Jasmin
open Cmdliner
open CommonCLI
open Utils

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
         A.pp_extended_op_for_rocq fmt;
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
