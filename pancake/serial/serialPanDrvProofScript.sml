(*
a
*)
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
   (* IS_SOME(read_bytearray base_addr 8 (mem_load_byte mem memaddrs be)) ∧*)
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
  rpt strip_tac >>
  fs[Once evaluate_def,uart_init_state_def,serialProg_def,
     uart_drv_getcharFun_def, uart_drv_putcharFun_def] >>
  fs[Once eval_def,flookup_fupdate_list,ALOOKUP_def,OPT_MMAP_def,lookup_code_def] >>
  fs[Once eval_def]
  (* TODO *)
QED

Theorem uart_drv_getcharFun_no_FinalFFI:
  ∀ck be mem memaddrs ffi base_addr.
    (∀f x x'. case call_FFI ffi "read_reg_UTRSTAT" x x' of
                FFI_final _ => F
              | FFI_return f _ =>
                  (∀f' x x'. call_FFI f "read_reg_URXH" x x' ≠ FFI_final f')) ⇒
    case evaluate (Call Tail (Label (strlit "uart_drv_getchar")) [],
               uart_init_state ck be mem memaddrs ffi base_addr) of
      (SOME (FinalFFI _),s') => F
    | _ => T
Proof
  rpt strip_tac >>
  simp[Once evaluate_def,uart_init_state_def,serialProg_def,
       uart_drv_getcharFun_def, uart_drv_putcharFun_def] >>
  simp[Once eval_def,flookup_fupdate_list,ALOOKUP_def,OPT_MMAP_def,
       lookup_code_def] >>
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
  >- (unabbrev_all_tac >> fs[]) >>
  simp[] >>
  Cases_on ‘read_bytearray (base_addr + 64w) 32
            (mem_load_byte mem' memaddrs be)’
  >- (unabbrev_all_tac >>fs[]) >>
  fs[] >>
  Cases_on  ‘call_FFI ffi "read_reg_UTRSTAT" x x'’
  >- (simp[]>>unabbrev_all_tac >> fs[]>>
      fs[OPTION_MAP_DEF, OPTION_BIND_def, FLOOKUP_UPDATE,
         wordLangTheory.word_sh_def, wordLangTheory.word_op_def,
         OPT_MMAP_def, eval_def, evaluate_def]>>
      Cases_on ‘mem_stores (base_addr + 128w)
                (flatten (ValWord 0w)) memaddrs
                (write_bytearray (base_addr + 64w) l mem'
                 memaddrs be)’
      >> fs[OPTION_MAP_DEF, OPTION_BIND_def, FLOOKUP_UPDATE,
            wordLangTheory.word_sh_def, wordLangTheory.word_op_def,
            OPT_MMAP_def, eval_def, evaluate_def]>>
      Cases_on ‘mem_store_byte x'' memaddrs be
                (base_addr + 160w) (w2w (base_addr + 64w))’
      >> fs[OPTION_MAP_DEF, OPTION_BIND_def, FLOOKUP_UPDATE,
            wordLangTheory.word_sh_def, wordLangTheory.word_op_def,
            OPT_MMAP_def, eval_def, evaluate_def]>>
      Cases_on ‘mem_store_byte x'³' memaddrs be
                (base_addr + 168w) (w2w (base_addr + 72w))’
      >> fs[OPTION_MAP_DEF, OPTION_BIND_def, FLOOKUP_UPDATE,
            wordLangTheory.word_sh_def, wordLangTheory.word_op_def,
            OPT_MMAP_def, eval_def, evaluate_def]>>
      Cases_on ‘mem_store_byte x'⁴' memaddrs be
                (base_addr + 176w) (w2w (base_addr + 80w))’
      >> fs[OPTION_MAP_DEF, OPTION_BIND_def, FLOOKUP_UPDATE,
            wordLangTheory.word_sh_def, wordLangTheory.word_op_def,
            OPT_MMAP_def, eval_def, evaluate_def]>>
      Cases_on ‘mem_store_byte x'⁵' memaddrs be
                (base_addr + 184w) (w2w (base_addr + 88w))’
      >> fs[OPTION_MAP_DEF, OPTION_BIND_def, FLOOKUP_UPDATE,
            wordLangTheory.word_sh_def, wordLangTheory.word_op_def,
            OPT_MMAP_def, eval_def, evaluate_def]>>
      Cases_on ‘mem_load One (base_addr + 128w) memaddrs x'⁶'’
      >- fs[OPTION_MAP_DEF, OPTION_BIND_def, FLOOKUP_UPDATE,
            wordLangTheory.word_sh_def, wordLangTheory.word_op_def,
            OPT_MMAP_def, eval_def, evaluate_def]>>
      Cases_on ‘x'⁷'’>>fs[]
      >- (fs[OPTION_MAP_DEF, OPTION_BIND_def, FLOOKUP_UPDATE,
             wordLangTheory.word_sh_def, wordLangTheory.word_op_def,
             OPT_MMAP_def, eval_def, evaluate_def]>>
          Cases_on ‘w’>>fs[]
          >-(fs[OPTION_MAP_DEF, OPTION_BIND_def, FLOOKUP_UPDATE,
                wordLangTheory.word_sh_def, wordLangTheory.word_op_def,
                OPT_MMAP_def, eval_def, evaluate_def]>>
             IF_CASES_TAC>>simp[]
             >-(fs[OPTION_MAP_DEF, OPTION_BIND_def, FLOOKUP_UPDATE,
                   wordLangTheory.word_sh_def, wordLangTheory.word_op_def,
                   OPT_MMAP_def, eval_def, evaluate_def]>>
                Cases_on ‘read_bytearray base_addr 8
                          (mem_load_byte x'⁶' memaddrs be)’
                >> fs[]>>
                Cases_on ‘read_bytearray (base_addr + 64w) 32
                          (mem_load_byte x'⁶' memaddrs be)’
                >> fs[] >>
                Cases_on ‘call_FFI f "read_reg_URXH" x'⁷' x'⁸'’
                >- (fs[FLOOKUP_UPDATE]
                    >>Cases_on ‘mem_load_byte
                                (write_bytearray (base_addr + 64w) l' x'⁶'
                                 memaddrs be) memaddrs be (base_addr + 64w)’
                    >- (simp[shape_of_def, size_of_shape_def])>>
                    fs[]>>simp[shape_of_def, size_of_shape_def])>>
                simp[shape_of_def, size_of_shape_def, FLOOKUP_UPDATE]>>
                first_assum(qspecl_then [‘x’, ‘x'’] assume_tac)>>
                Cases_on ‘call_FFI ffi "read_reg_UTRSTAT" x x'’>>gs[])>>
                simp[Once evaluate_def]>>fs[eval_def, FLOOKUP_UPDATE]>>
             simp[shape_of_def, size_of_shape_def])))>>
  unabbrev_all_tac >> fs[]>>
  first_assum(qspecl_then [‘x’, ‘x'’] assume_tac)>>
  Cases_on ‘call_FFI ffi "read_reg_UTRSTAT" x x'’>> gs[]
QED

Theorem uart_drv_getcharFun_no_None:
  ∀ck be mem memaddrs ffi base_addr res s.
    IS_SOME(read_bytearray base_addr 8 (mem_load_byte mem memaddrs be)) ∧
    IS_SOME(read_bytearray (base_addr + 64w) 32
                           (mem_load_byte mem memaddrs be)) ∧
    (∀r x x' f y. call_FFI ffi r x x' ≠ FFI_return f y) ⇒
    case evaluate (Call Tail (Label (strlit "uart_drv_getchar")) [],
               uart_init_state ck be mem memaddrs ffi base_addr) of
      (NONE : 64 result option,s') => F
    | _ => T
Proof
  rpt strip_tac >>
  simp[Once evaluate_def,uart_init_state_def,serialProg_def,
       uart_drv_getcharFun_def, uart_drv_putcharFun_def] >>
  simp[Once eval_def,flookup_fupdate_list,ALOOKUP_def,
       OPT_MMAP_def,lookup_code_def] >>
  IF_CASES_TAC >- simp[] >>
  simp[dec_clock_def] >>
  simp[evaluate_def, eval_def,OPT_MMAP_def,wordLangTheory.word_op_def,
       FLOOKUP_UPDATE] >>
  Cases_on ‘read_bytearray base_addr 8 (mem_load_byte mem' memaddrs be)’>>
  fs[]>>
  Cases_on ‘read_bytearray (base_addr + 64w) 32
            (mem_load_byte mem' memaddrs be)’ >>
  fs[] >>
  Cases_on  ‘call_FFI ffi "read_reg_UTRSTAT" x x'’>>
  gs[]
QED

val _ = export_theory();
