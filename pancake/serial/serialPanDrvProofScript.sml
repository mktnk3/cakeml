open preamble backendTheory panLangTheory word_to_wordTheory pan_to_wordTheory;
open serialPanDrvTheory panSemTheory;

val _ = new_theory "serialPanDrvProof"

Definition uart_device_oracle_def:
  uart_device_oracle = ARB (* TODO (eventually) *)
End

Definition uart_init_state_def:
  uart_init_state ck be mem memaddrs ffi base_addr =
  <| locals := FEMPTY;
     code := FEMPTY |++ serialProg;
     eshapes := FEMPTY; (* TODO: should there be something here? *)
     memory := mem;
     memaddrs := memaddrs;
     clock := ck;
     be := be;
     ffi := ffi;
     base_addr := base_addr
    |>
End

Theorem uart_drv_getcharFun_no_break:
  ∀ck be mem memaddrs ffi res s.
    (evaluate (Call Tail (Label (strlit "uart_drv_getchar")) [],
               uart_init_state ck be mem memaddrs ffi) = (res,s)) ∧
    preconditions (* TODO *) ⇒
    res ≠ SOME Break
Proof
  cheat
  (* TODO *)
QED

Theorem uart_drv_getcharFun_no_error:
  ∀ck be mem memaddrs ffi base_addr res s.
    IS_SOME(read_bytearray base_addr 8 (mem_load_byte mem memaddrs be)) ∧
    more preconditions (* TODO *) ⇒
    case evaluate (Call Tail (Label (strlit "uart_drv_getchar")) [],
               uart_init_state ck be mem memaddrs ffi base_addr) of
      (SOME Error,s') => F
    | _ => T
Proof
  rpt strip_tac >>
  simp[Once evaluate_def,uart_init_state_def,serialProg_def,
     uart_drv_getcharFun_def, uart_drv_putcharFun_def] >>
  simp[Once eval_def,flookup_fupdate_list,ALOOKUP_def,OPT_MMAP_def,lookup_code_def] >>
  IF_CASES_TAC >- simp[] >>
  simp[dec_clock_def] >>
  simp[Once evaluate_def] >>
  simp[Once eval_def] >>
  qmatch_goalsub_abbrev_tac ‘a1 (evaluate _)’ >>
  simp[Once evaluate_def] >>
  simp[eval_def,OPT_MMAP_def,wordLangTheory.word_op_def] >>
  qmatch_goalsub_abbrev_tac ‘a2 (evaluate _)’ >>
  simp[Once evaluate_def,eval_def] >>
  qmatch_goalsub_abbrev_tac ‘a3 (evaluate _)’ >>
  simp[Once evaluate_def,eval_def] >>
  qmatch_goalsub_abbrev_tac ‘a4 (evaluate _)’ >>
  simp[Once evaluate_def,eval_def] >>
  qmatch_goalsub_abbrev_tac ‘a5 (evaluate _)’ >>
  simp[Once evaluate_def,eval_def] >>
  qmatch_goalsub_abbrev_tac ‘a6 (evaluate _)’ >>
  simp[Once evaluate_def,FLOOKUP_UPDATE] >>
  Cases_on ‘read_bytearray base_addr 8 (mem_load_byte mem' memaddrs be)’
  >- (simp[] >>
      unabbrev_all_tac >>
      fs[]) >>
  simp[] >>
  cheat (* TODO *)
QED

Theorem uart_drv_getcharFun_no_error:
  ∀ck be mem memaddrs ffi res s.
    (evaluate (Call Tail (Label (strlit "uart_drv_getchar")) [],
               uart_init_state ck be mem memaddrs ffi) = (res,s)) ∧
    preconditions (* TODO *) ⇒
    res ≠ SOME Error
Proof
  rpt strip_tac >>
  fs[Once evaluate_def,uart_init_state_def,serialProg_def,
     uart_drv_getcharFun_def, uart_drv_putcharFun_def] >>
  fs[Once eval_def,flookup_fupdate_list,ALOOKUP_def,OPT_MMAP_def,lookup_code_def] >>
  fs[Once eval_def]
  (* TODO *)
QED

val _ = export_theory();
