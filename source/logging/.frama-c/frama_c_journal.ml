(* Frama-C journal generated at 23:16 the 15/06/2019 *)

exception Unreachable
exception Exception of string

[@@@ warning "-26"]

(* Run the user commands *)
let run () =
  Dynamic.Parameter.Bool.set "-lib-entry" true;
  Dynamic.Parameter.Bool.set "-c11" true;
  Dynamic.Parameter.String.set "-cpp-extra-args"
    "-I. -I../../FreeRTOS-mirror/FreeRTOS/Demo/RISC-V_Galois_P1 -I../../FreeRTOS-mirror/FreeRTOS/Source/include -I../../FreeRTOS-mirror/FreeRTOS/Source/portable/GCC/RISC-V -I../../FreeRTOS-mirror/FreeRTOS/Demo/RISC-V_Galois_P1/demo -I../../FreeRTOS-mirror/FreeRTOS/Demo/RISC-V_Galois_P1/bsp -I../../FreeRTOS-mirror/FreeRTOS/Demo/RISC-V_Galois_P1/devices -D__riscv_xlen=32";
  Dynamic.Parameter.String.set "" "log.c,secure_log.c";
  File.init_from_cmdline ();
  Project.set_keep_current false;
  ()

(* Main *)
let main () =
  Journal.keep_file "./.frama-c/frama_c_journal.ml";
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
