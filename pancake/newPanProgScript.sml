open preamble backendTheory panLangTheory word_to_wordTheory pan_to_wordTheory x64_configTheory compilationLib;

val _ = new_theory "newPanProg";

(* val testPanProg =
 “[
    (
      (strlit "func_one"),
      [(strlit "x", One)],
      panLang$Dec (strlit "x") (panLang$Const 9w) (panLang$Return (panLang$Var (strlit "x")) :64 panLang$prog)
    )
  ]”; 

val testPanProg =
 “[
    (
      (strlit "func_one"),
      [] :(mlstring # shape) list,
      panLang$Skip :64 panLang$prog
    )
  ]”; *)


val testPanProg =
 “[ 
    (
      (strlit "func_one"),
      [] :(mlstring # shape) list,
      panLang$Dec (strlit "a") (Const 0w) (
        panLang$Dec (strlit "b") (Const 1w) (
          panLang$Dec (strlit "c") (Const 4w) (
            panLang$Dec (strlit "d") (Const 3w) (
              ExtCall (strlit "out_morefun") (strlit "a") (strlit "b") (strlit "c") (strlit "d")) :64 panLang$prog)))
    );
    (
      (strlit "func_two"),
      [] :(mlstring # shape) list,
      panLang$Dec (strlit "a") (Const 0w) (
        panLang$Dec (strlit "b") (Const 1w) (
          panLang$Dec (strlit "c") (Const 4w) (
            panLang$Dec (strlit "d") (Const 3w) (
              ExtCall (strlit "out_fun") (strlit "a") (strlit "b") (strlit "c") (strlit "d")) :64 panLang$prog)))
    );
    (
     (strlit "func_three"),
     [] :(mlstring # shape) list,
     panLang$Dec (strlit "a") (Const 0w) (
       panLang$Dec (strlit "b") (Const 1w) (
         panLang$Dec (strlit "c") (Const 4w) (
           panLang$Dec (strlit "d") (Const 3w) (
             ExtCall (strlit "out_fun") (strlit "a") (strlit "b") (strlit "c") (strlit "d")) :64 panLang$prog)))
    )
  ]”;

                    
val testWordProg =
  EVAL “pan_to_word$compile_prog ^testPanProg” |> concl |> rhs;

(* first value in pair is the colouring for register alloc *)
val (something, wordyWordProg)  = EVAL
  “word_to_word$compile x64_backend_config.word_to_word_conf x64_backend_config.lab_conf.asm_conf ^testWordProg”
  |> concl |> rhs |> dest_pair;


(*
  Begin stuff pillaged from compilationLib
 *)
 open preamble backendTheory
     arm7_compileLib export_arm7Theory
     arm8_compileLib export_arm8Theory
     mips_compileLib export_mipsTheory
     riscv_compileLib export_riscvTheory
     ag32_compileLib export_ag32Theory
     x64_compileLib export_x64Theory

val cs = compilation_compset()

val () =
      computeLib.extend_compset [
        computeLib.Extenders [
          arm7_targetLib.add_arm7_encode_compset,
          arm8_targetLib.add_arm8_encode_compset,
          mips_targetLib.add_mips_encode_compset,
          riscv_targetLib.add_riscv_encode_compset,
          ag32_targetLib.add_ag32_encode_compset,
          x64_targetLib.add_x64_encode_compset],
        computeLib.Defs [
          arm7_backend_config_def, arm7_names_def,
          arm8_backend_config_def, arm8_names_def,
          mips_backend_config_def, mips_names_def,
          riscv_backend_config_def, riscv_names_def,
          ag32_backend_config_def, ag32_names_def,
          x64_backend_config_def, x64_names_def
          ]
      ] cs

val eval = computeLib.CBV_CONV cs;
fun parl f = parlist (!num_threads) (!chunk_size) f


val conf_tm = “x64_backend_config”

val stack_prog = “from_word x64_backend_config LN ^wordyWordProg”
                   |> (REWRITE_CONV [from_word_def]
                       THENC ONCE_REWRITE_CONV[LET_DEF]
                       THENC (DEPTH_CONV BETA_CONV)
                       THENC (RAND_CONV eval)
                       THENC SIMP_CONV std_ss [ELIM_UNCURRY,FST,SND])

val lab_prog = stack_prog
        |> concl |> rhs
        |> (REWRITE_CONV [from_stack_def]
            THENC ONCE_REWRITE_CONV[LET_DEF]
            THENC (DEPTH_CONV BETA_CONV)
            THENC (RAND_CONV eval))

val target_prog = lab_prog
        |> concl |> rhs
        |> (REWRITE_CONV [from_lab_def]
            THENC ONCE_REWRITE_CONV[LET_DEF]
            THENC (DEPTH_CONV BETA_CONV)
            THENC (RAND_CONV eval))

val finRes =
  eval “from_word (x64_backend_config with clos_conf updated_by (λc. c with start := first_name)) LN ^wordyWordProg”;


(*    
val testCompPan =
  EVAL “pan_to_target$compile_prog x64_backend_config ^testPanProg”;
*)


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
