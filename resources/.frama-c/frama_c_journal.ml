(* Frama-C journal generated at 17:37 the 14/12/2020 *)

exception Unreachable
exception Exception of string

[@@@ warning "-26"]

(* Run the user commands *)
let run () =
  Dynamic.Parameter.Bool.set "-wp" true;
  Dynamic.Parameter.String.set ""
    "/media/sf_Formal-Approaches/resources/sort_1.c";
  begin try
    (* exception Log.AbortError("kernel") raised on:  *)
    File.init_from_cmdline ();
    raise Unreachable
  with
  | Unreachable as exn -> raise exn
  | exn (* Log.AbortError("kernel") *) ->
    (* continuing: *) raise (Exception (Printexc.to_string exn))
  end

(* Main *)
let main () =
  Journal.keep_file ".frama-c/frama_c_journal.ml";
  try run ()
  with
  | Unreachable -> Kernel.fatal "Journal reaches an assumed dead code" 
  | Exception s -> Kernel.log "Journal re-raised the exception %S" s
  | exn ->
    Kernel.fatal
      "Journal raised an unexpected exception: %s"
      (Printexc.to_string exn)

(* Registering *)
let main : unit -> unit =
  Dynamic.register
    ~plugin:"Frama_c_journal.ml"
    "main"
    (Datatype.func Datatype.unit Datatype.unit)
    ~journalize:false
    main

(* Hooking *)
let () = Cmdline.run_after_loading_stage main; Cmdline.is_going_to_load ()
