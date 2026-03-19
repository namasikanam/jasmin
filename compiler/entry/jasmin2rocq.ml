open Jasmin
open Cmdliner
open CommonCLI
open Utils

let parse_and_extract arch call_conv idirs =
  let module A = (val CoreArchFactory.get_arch_module arch call_conv) in
  let extract output file warn =
    if not warn then nowarning ();
    let prog = parse_and_compile (module A) ~wi2i:false Compiler.ParamsExpansion file idirs in
    let fmt, close =
      match output with
      | None -> (Format.std_formatter, fun () -> ())
      | Some f ->
          let out = open_out f in
          let fmt = Format.formatter_of_out_channel out in
          (fmt, fun () -> close_out out)
    in
    BatPervasives.finally
      (fun () -> close ())
      (fun () ->
        Printer.pp_prog_rocq ~debug:true A.reg_size A.msf_size A.asmOp fmt prog)
      ()
  in
  fun output file warn ->
    match extract output file warn with
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

let file =
  let doc = "The Jasmin source file to extract" in
  Arg.(required & pos 0 (some non_dir_file) None & info [] ~docv:"JAZZ" ~doc)

let () =
  let doc = "Extract Jasmin program to Rocq (Coq) notation" in
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
      $ output $ file $ warn)
  |> Cmd.eval |> exit
