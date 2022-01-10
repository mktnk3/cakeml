open preamble backendTheory panLangTheory word_to_wordTheory pan_to_wordTheory x64_configTheory compilationLib;

val _ = new_theory "serialPanDrv";

(*
Device register offsets from original driver:
https://github.com/seL4/seL4/blob/master/src/drivers/serial/exynos4210-uart.c

#define ULCON       0x0000 /* line control */
#define UCON        0x0004 /* control */
#define UFCON       0x0008 /* fifo control */
#define UMCON       0x000C /* modem control */
#define UTRSTAT     0x0010 /* TX/RX status */
#define UERSTAT     0x0014 /* RX error status */
#define UFSTAT      0x0018 /* FIFO status */
#define UMSTAT      0x001C /* modem status */
#define UTXH        0x0020 /* TX buffer */
#define URXH        0x0024 /* RX buffer */
#define UBRDIV      0x0028 /* baud rate divisor */
#define UFRACVAL    0x002C /* divisor fractional value */
#define UINTP       0x0030 /* interrupt pending */
#define UINTSP      0x0034 /* interrupt source pending */
#define UINTM       0x0038 /* interrupt mask */
*)

val RXBUF_READY_const= “(Shift Lsl (Const 1w) 0) :64 panLang$exp”;
val TXBUF_EMPTY_const= “(Shift Lsl (Const 1w) 1) :64 panLang$exp”;
val TX_EMPTY_const= “(Shift Lsl (Const 1w) 2) : 64 panLang$exp”;

val minus_one_const= “(panLang$Const $ n2w $ 2**64 - 1) :64 panLang$exp” |> EVAL |> concl |> rhs;

val uart_drv_putcharFun=
  “(strlit "uart_drv_putchar",
    [(strlit "c", One)],
    Seq 
    (Dec (strlit "a1") BaseAddr (
      Dec (strlit "a2") (Op Add [BaseAddr; Const 64w]) (
        Dec (strlit "l1") (Const 1w) (
          Dec (strlit "l2") (Const 32w) (
            Seq
              (While (Const 1w) (
                Seq 
                  (ExtCall (strlit $ "read_reg_UTRSTAT") (strlit "a1") (strlit "l1") (strlit "a2") (strlit "l2"))
                  (If (Cmp Equal (Op And [Load One (Var $ strlit "a2"); ^TXBUF_EMPTY_const]) (Const 0w)) Skip Break)      
              ))
              (Seq
                (StoreByte BaseAddr (Var $ strlit "c")) 
                (ExtCall (strlit "write_reg_UTXH") (strlit "a1") (strlit "l1") (strlit "a2") (strlit "l2"))
              )
    )))))
    (Return $ Const 0w) :64 panLang$prog
   )”; (* Note: original function does not return a value. *)
    
val uart_drv_getcharFun=
  “(strlit "uart_drv_getchar",
    [] :(mlstring # shape) list,     
    Dec (strlit "a1") BaseAddr (
      Dec (strlit "a2") (Op Add [BaseAddr; Const 64w]) (
        Dec (strlit "l1") (Const 1w) (
          Dec (strlit "l2") (Const 32w) (
            Seq               
              (ExtCall (strlit $ "read_reg_UTRSTAT") (strlit "a1") (strlit "l1") (strlit "a2") (strlit "l2"))
              (If (Op And [Load One (Var $ strlit "a2"); ^RXBUF_READY_const])
                (Seq
                  (ExtCall (strlit $ "read_reg_URXH") (strlit "a1") (strlit "l1") (strlit "a2") (strlit "l2"))
                  (Return (LoadByte (Var $ strlit "a2"))))
                (Return ^minus_one_const)
              )     
    )))) :64 panLang$prog
   )”;

val serialProg= “[^uart_drv_putcharFun; ^uart_drv_getcharFun]”;

(* Driver set-up seems to occur somewhere else. *)   

(* ======================================================================================================= *)

(* modified from time_eval *)
Definition comp_def:
  comp prog =
    let word_prog = pan_to_word$compile_prog prog in
    let c = x64_backend_config in
    let c = c with clos_conf updated_by (λc. c with start := first_name) in
      from_word_0 c LN word_prog
End

fun compile name prog = let
  fun ABBREV_CONV name tm = SYM (mk_abbrev name tm);
  val to_word_0_thm =
    “comp ^prog”
    |> REWR_CONV comp_def
    |> CONV_RULE (PATH_CONV "rr" EVAL THENC
                  PATH_CONV "r" (REWR_CONV LET_THM) THENC
                  PATH_CONV "r" BETA_CONV)
    |> SIMP_RULE std_ss [crep_to_loopTheory.first_name_def,LET_THM]
    |> CONV_RULE (PATH_CONV "rr" (ABBREV_CONV "word_0_p"))
    |> CONV_RULE (PATH_CONV "rlr" (ABBREV_CONV "word_0_names"))
    |> CONV_RULE (PATH_CONV "rllr" (ABBREV_CONV "word_0_c"))
  val conf_tm = x64_backend_config_def |> concl |> dest_eq |> fst
  val word_0_tm = “(word_0_c, word_0_p, word_0_names)”
  val lab_prog_name = name
  val stack_to_lab_thm = compile_to_lab_new conf_tm word_0_tm lab_prog_name;
  val lab_prog_def = definition(mk_abbrev_name lab_prog_name)
  val code_name = (!intermediate_prog_prefix) ^ "code"
  val data_name = (!intermediate_prog_prefix) ^ "data"
  val config_name = (!intermediate_prog_prefix) ^ "config";
  val cbv_to_bytes = cbv_to_bytes_x64
  val from_word_0_thm =
    cbv_to_bytes stack_to_lab_thm lab_prog_def code_name
                 data_name config_name (name^".S");
  in from_word_0_thm end

val _ = export_theory();
