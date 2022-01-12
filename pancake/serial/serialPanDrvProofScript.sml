open preamble backendTheory panLangTheory word_to_wordTheory pan_to_wordTheory x64_configTheory compilationLib;
open serialPanDrvTheory panSemTheory;

val _ = new_theory "serialPanDrvProof"

Definition uart_device_oracle_def:
  uart_device_oracle = ARB (* TODO (eventually) *)
End

Definition uart_init_state_def:
  uart_init_state ck be mem memaddrs ffi =
  <| locals := FEMPTY;
     code := FEMPTY |++ serialProg;
     eshapes := FEMPTY; (* TODO: should there be something here? *)
     memory := mem;
     memaddrs := memaddrs;
     clock := ck;
     be := be;
     ffi := ffi
    |> 
End

Theorem uart_drv_getcharFun_no_break:
  ∀ck be mem memaddrs ffi res s.
    (evaluate (Call Tail (Label (strlit "uart_drv_getchar")) [],
               uart_init_state ck be mem memaddrs ffi) = (res,s)) ∧
    preconditions (* TODO *) ⇒
    res ≠ SOME Break
Proof
  (* TODO *)
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
  fs[Once eval_def,flookup_fupdate_list,ALOOKUP_def] >>
  (* TODO *)
QED

val _ = export_theory();
