(*

composing semantics correctness from pan to target

*)

open preamble
     backendProofTheory pan_to_wordProofTheory
     pan_to_targetTheory

val _ = new_theory "pan_to_targetProof";

Overload stack_remove_prog_comp[local] = ``stack_remove$prog_comp``
Overload stack_alloc_prog_comp[local] = ``stack_alloc$prog_comp``
Overload stack_names_prog_comp[local] = ``stack_names$prog_comp``
Overload word_to_word_compile[local] = ``word_to_word$compile``
Overload word_to_stack_compile[local] = ``word_to_stack$compile``
Overload stack_to_lab_compile[local] = ``stack_to_lab$compile``
Overload pan_to_word_compile_prog[local] = ``pan_to_word$compile_prog
``

Theorem loop_to_word_comp_no_install:
  wprog = loop_to_word$comp ctxt prog l ⇒
  no_install (FST wprog)
Proof
  MAP_EVERY qid_spec_tac [‘wprog’, ‘l’, ‘prog’, ‘ctxt’]>>
  recInduct loop_to_wordTheory.comp_ind>>
  gs[loop_to_wordTheory.comp_def, wordPropsTheory.no_install_def]>>
  rw[]>>
  TRY (pairarg_tac>>gs[]>>
       pairarg_tac>>gs[]>>
       gs[wordPropsTheory.no_install_def])>>
  TRY (rpt (CASE_TAC>>gs[wordPropsTheory.no_install_def]))>>
  rpt (pairarg_tac>>gs[wordPropsTheory.no_install_def])
QED

Theorem loop_to_word_comp_func_no_install:
  no_install (comp_func name params body)
Proof
  MAP_EVERY qid_spec_tac [‘wprog’, ‘name’, ‘params’, ‘body’]>>Induct>>
  gs[loop_to_wordTheory.comp_func_def]>>
  gs[loop_to_wordTheory.comp_def, wordPropsTheory.no_install_def]>>
  rw[loop_to_word_comp_no_install]>>
  TRY (last_x_assum (qspecl_then [‘params’, ‘name’] assume_tac)>>
       gs[loopLangTheory.acc_vars_def])>>
  TRY (last_x_assum (qspecl_then [‘params’, ‘name’] assume_tac)>>
       pairarg_tac>>gs[]>>
       pairarg_tac>>
       gs[wordPropsTheory.no_install_def]>>
       last_x_assum (qspecl_then [‘params’, ‘name’] assume_tac)>>
       rpt (qpat_x_assum ‘comp _ _ _ = _’ (assume_tac o GSYM))>>
       drule loop_to_word_comp_no_install>>gs[]>> 
       qpat_x_assum ‘(wp, _) = _’ kall_tac>>
       drule loop_to_word_comp_no_install>>gs[])>>
  rpt (CASE_TAC>>gs[wordPropsTheory.no_install_def])>>
  pairarg_tac>>gs[]>>
  pairarg_tac>>
  gs[wordPropsTheory.no_install_def]>> 
  rpt (qpat_x_assum ‘comp _ _ _ = _’ (assume_tac o GSYM))>>
  drule loop_to_word_comp_no_install>>gs[]>> 
  qpat_x_assum ‘(p1, _) = _’ kall_tac>>
  drule loop_to_word_comp_no_install>>gs[]
QED

Theorem loop_to_word_compile_no_install:
  wprog = loop_to_word$compile_prog pan_prog ⇒
  EVERY no_install (MAP (SND o SND) wprog)
Proof
  qid_spec_tac ‘wprog’>>
  Induct_on ‘pan_prog’>>
  gs[loop_to_wordTheory.compile_def, loop_to_wordTheory.compile_prog_def]>>
  strip_tac>>pairarg_tac>>gs[loop_to_word_comp_func_no_install]
QED

Theorem loop_compile_no_install_code:
  loop_to_word$compile prog = prog' ⇒
  no_install_code (fromAList prog')
Proof
  disch_then (assume_tac o GSYM)>>
  gs[loop_to_wordTheory.compile_def]>>
  drule loop_to_word_compile_no_install>>
  rw[wordPropsTheory.no_install_code_def]>>
  gs[lookup_fromAList, EVERY_MEM, MEM_MAP]>>
  drule ALOOKUP_MEM>>strip_tac>>
  first_x_assum (qspec_then ‘p’ assume_tac)>>
  res_tac>>gs[]
QED
        
Theorem loop_to_word_comp_no_alloc:
  wprog = loop_to_word$comp ctxt prog l ⇒
  no_alloc (FST wprog)
Proof
  MAP_EVERY qid_spec_tac [‘wprog’, ‘l’, ‘prog’, ‘ctxt’]>>
  recInduct loop_to_wordTheory.comp_ind>>
  gs[loop_to_wordTheory.comp_def, wordPropsTheory.no_alloc_def]>>
  rw[]>>
  TRY (pairarg_tac>>gs[]>>
       pairarg_tac>>gs[]>>
       gs[wordPropsTheory.no_alloc_def])>>
  TRY (rpt (CASE_TAC>>gs[wordPropsTheory.no_alloc_def]))>>
  rpt (pairarg_tac>>gs[wordPropsTheory.no_alloc_def])
QED

Theorem loop_to_word_comp_func_no_alloc:
  no_alloc (comp_func name params body)
Proof
  MAP_EVERY qid_spec_tac [‘wprog’, ‘name’, ‘params’, ‘body’]>>Induct>>
  gs[loop_to_wordTheory.comp_func_def]>>
  gs[loop_to_wordTheory.comp_def, wordPropsTheory.no_alloc_def]>>
  rw[loop_to_word_comp_no_alloc]>>
  TRY (last_x_assum (qspecl_then [‘params’, ‘name’] assume_tac)>>
       gs[loopLangTheory.acc_vars_def])>>
  TRY (last_x_assum (qspecl_then [‘params’, ‘name’] assume_tac)>>
       pairarg_tac>>gs[]>>
       pairarg_tac>>
       gs[wordPropsTheory.no_alloc_def]>>
       last_x_assum (qspecl_then [‘params’, ‘name’] assume_tac)>>
       rpt (qpat_x_assum ‘comp _ _ _ = _’ (assume_tac o GSYM))>>
       drule loop_to_word_comp_no_alloc>>gs[]>> 
       qpat_x_assum ‘(wp, _) = _’ kall_tac>>
       drule loop_to_word_comp_no_alloc>>gs[])>>
  rpt (CASE_TAC>>gs[wordPropsTheory.no_alloc_def])>>
  pairarg_tac>>gs[]>>
  pairarg_tac>>
  gs[wordPropsTheory.no_alloc_def]>> 
  rpt (qpat_x_assum ‘comp _ _ _ = _’ (assume_tac o GSYM))>>
  drule loop_to_word_comp_no_alloc>>gs[]>> 
  qpat_x_assum ‘(p1, _) = _’ kall_tac>>
  drule loop_to_word_comp_no_alloc>>gs[]
QED

Theorem loop_to_word_compile_no_alloc:
  wprog = loop_to_word$compile_prog pan_prog ⇒
  EVERY no_alloc (MAP (SND o SND) wprog)
Proof
  qid_spec_tac ‘wprog’>>
  Induct_on ‘pan_prog’>>
  gs[loop_to_wordTheory.compile_def, loop_to_wordTheory.compile_prog_def]>>
  strip_tac>>pairarg_tac>>gs[loop_to_word_comp_func_no_alloc]
QED

Theorem loop_compile_no_alloc_code:
  loop_to_word$compile prog = prog' ⇒
  no_alloc_code (fromAList prog')
Proof
  disch_then (assume_tac o GSYM)>>
  gs[loop_to_wordTheory.compile_def]>>
  drule loop_to_word_compile_no_alloc>>
  rw[wordPropsTheory.no_alloc_code_def]>>
  gs[lookup_fromAList, EVERY_MEM, MEM_MAP]>>
  drule ALOOKUP_MEM>>strip_tac>>
  first_x_assum (qspec_then ‘p’ assume_tac)>>
  res_tac>>gs[]
QED

Theorem loop_to_word_comp_no_mt:
  wprog = loop_to_word$comp ctxt prog l ⇒
  no_mt (FST wprog)
Proof
  MAP_EVERY qid_spec_tac [‘wprog’, ‘l’, ‘prog’, ‘ctxt’]>>
  recInduct loop_to_wordTheory.comp_ind>>
  gs[loop_to_wordTheory.comp_def, wordPropsTheory.no_mt_def]>>
  rw[]>>
  TRY (pairarg_tac>>gs[]>>
       pairarg_tac>>gs[]>>
       gs[wordPropsTheory.no_mt_def])>>
  TRY (rpt (CASE_TAC>>gs[wordPropsTheory.no_mt_def]))>>
  rpt (pairarg_tac>>gs[wordPropsTheory.no_mt_def])
QED

Theorem loop_to_word_comp_func_no_mt:
  no_mt (comp_func name params body)
Proof
  MAP_EVERY qid_spec_tac [‘wprog’, ‘name’, ‘params’, ‘body’]>>Induct>>
  gs[loop_to_wordTheory.comp_func_def]>>
  gs[loop_to_wordTheory.comp_def, wordPropsTheory.no_mt_def]>>
  rw[loop_to_word_comp_no_mt]>>
  TRY (last_x_assum (qspecl_then [‘params’, ‘name’] assume_tac)>>
       gs[loopLangTheory.acc_vars_def])>>
  TRY (last_x_assum (qspecl_then [‘params’, ‘name’] assume_tac)>>
       pairarg_tac>>gs[]>>
       pairarg_tac>>
       gs[wordPropsTheory.no_mt_def]>>
       last_x_assum (qspecl_then [‘params’, ‘name’] assume_tac)>>
       rpt (qpat_x_assum ‘comp _ _ _ = _’ (assume_tac o GSYM))>>
       drule loop_to_word_comp_no_mt>>gs[]>> 
       qpat_x_assum ‘(wp, _) = _’ kall_tac>>
       drule loop_to_word_comp_no_mt>>gs[])>>
  rpt (CASE_TAC>>gs[wordPropsTheory.no_mt_def])>>
  pairarg_tac>>gs[]>>
  pairarg_tac>>
  gs[wordPropsTheory.no_mt_def]>> 
  rpt (qpat_x_assum ‘comp _ _ _ = _’ (assume_tac o GSYM))>>
  drule loop_to_word_comp_no_mt>>gs[]>> 
  qpat_x_assum ‘(p1, _) = _’ kall_tac>>
  drule loop_to_word_comp_no_mt>>gs[]
QED

Theorem loop_to_word_compile_no_mt:
  wprog = loop_to_word$compile_prog pan_prog ⇒
  EVERY no_mt (MAP (SND o SND) wprog)
Proof
  qid_spec_tac ‘wprog’>>
  Induct_on ‘pan_prog’>>
  gs[loop_to_wordTheory.compile_def, loop_to_wordTheory.compile_prog_def]>>
  strip_tac>>pairarg_tac>>gs[loop_to_word_comp_func_no_mt]
QED

Theorem loop_compile_no_mt_code:
  loop_to_word$compile prog = prog' ⇒
  no_mt_code (fromAList prog')
Proof
  disch_then (assume_tac o GSYM)>>
  gs[loop_to_wordTheory.compile_def]>>
  drule loop_to_word_compile_no_mt>>
  rw[wordPropsTheory.no_mt_code_def]>>
  gs[lookup_fromAList, EVERY_MEM, MEM_MAP]>>
  drule ALOOKUP_MEM>>strip_tac>>
  first_x_assum (qspec_then ‘p’ assume_tac)>>
  res_tac>>gs[]
QED

Theorem pan_to_word_compile_prog_no_install_code:
  pan_to_word$compile_prog prog = prog' ⇒
  no_install_code (fromAList prog')
Proof
  gs[pan_to_wordTheory.compile_prog_def]>>strip_tac>>
  metis_tac[loop_compile_no_install_code]
QED
  
Theorem pan_to_word_compile_prog_no_alloc_code:
  pan_to_word$compile_prog prog = prog' ⇒
  no_alloc_code (fromAList prog')
Proof
  gs[pan_to_wordTheory.compile_prog_def]>>strip_tac>>
  metis_tac[loop_compile_no_alloc_code]
QED

Theorem pan_to_word_compile_prog_no_mt_code:
  pan_to_word$compile_prog prog = prog' ⇒
  no_mt_code (fromAList prog')
Proof
  gs[pan_to_wordTheory.compile_prog_def]>>strip_tac>>
  metis_tac[loop_compile_no_mt_code]
QED



(** implements' lemmas ***)

Theorem full_make_init_semantics2:
  full_make_init stack_conf data_conf max_heap sp offset bitmaps code (t:(α,β,γ) labSem$state)
  save_regs data_sp coracle = (s:(α,β,γ) stackSem$state ,opt) ∧
  good_dimindex (:α) ∧
  t.code =
  stack_to_lab_compile stack_conf data_conf max_heap sp offset code ∧
  t.compile_oracle =
  (λn.
     (let
        (c,p,b) = coracle n
      in
        (c,
         compile_no_stubs stack_conf.reg_names stack_conf.jump offset sp
                          p))) ∧ ¬t.failed ∧
  memory_assumption stack_conf.reg_names bitmaps data_sp t ∧
  max_stack_alloc ≤ max_heap ∧ t.link_reg ∉ save_regs ∧ t.pc = 0 ∧
  (∀k i n. k ∈ save_regs ⇒ t.io_regs n i k = NONE) ∧
  (∀k n. k ∈ save_regs ⇒ t.cc_regs n k = NONE) ∧
  (∀x. x ∈ t.mem_domain ⇒ w2n x MOD (dimindex (:α) DIV 8) = 0) ∧
  good_code sp code ∧ (∀n. good_code sp (FST (SND (coracle n)))) ∧
  10 ≤ sp ∧
  EVERY (λr. find_name stack_conf.reg_names (r + sp − 2) ∈ save_regs)
        [2; 3; 4] ∧ find_name stack_conf.reg_names 4 = t.len2_reg ∧
  find_name stack_conf.reg_names 3 = t.ptr2_reg ∧
  find_name stack_conf.reg_names 2 = t.len_reg ∧
  find_name stack_conf.reg_names 1 = t.ptr_reg ∧
  find_name stack_conf.reg_names 0 = t.link_reg ∧
  find_name stack_conf.reg_names PERMUTES 𝕌(:num) ⇒
  opt ≠ NONE ∧
  implements' T {labSem$semantics t} {semantics InitGlobals_location s}
Proof
  strip_tac>>
  drule_all stack_to_labProofTheory.full_make_init_semantics>>
  rpt strip_tac>>
  gs[semanticsPropsTheory.implements'_def,
     semanticsPropsTheory.extend_with_resource_limit'_def]
QED

Theorem word_to_stack_compile_semantics2:
  t.code =
  fromAList (SND (SND (SND (word_to_stack_compile asm_conf code)))) ∧
  k = asm_conf.reg_count − (5 + LENGTH asm_conf.avoid_regs) ∧
  init_state_ok k t coracle ∧
  ALOOKUP code raise_stub_location = NONE ∧
  ALOOKUP code store_consts_stub_location = NONE ∧
  FST (word_to_stack_compile asm_conf code) ≼ t.bitmaps ∧
  EVERY
  (λ(n,m,prog).
     flat_exp_conventions prog ∧
     post_alloc_conventions
     (asm_conf.reg_count − (5 + LENGTH asm_conf.avoid_regs)) prog)
  code ⇒
  implements'
  (word_lang_safe_for_space (make_init k t (fromAList code) coracle) start)
  {semantics start (t:(α,γ,'ffi) stackSem$state)}
   {semantics (make_init k t (fromAList code) coracle) start}
Proof
  strip_tac>>
  drule_then drule word_to_stackProofTheory.compile_semantics>>
  rpt (disch_then drule)>>
  rpt strip_tac>>
  gs[semanticsPropsTheory.implements'_def,
     semanticsPropsTheory.extend_with_resource_limit'_def]
QED

Theorem word_to_word_compile_semantics2:
  word_to_word_compile wconf acomf wprog0 = (col,wprog) ∧
  gc_fun_const_ok s.gc_fun ∧
  no_install_code (fromAList wprog0) ∧
  no_alloc_code (fromAList wprog0) ∧
  no_install_code s.code ∧
  no_alloc_code s.code ∧
  no_mt_code (fromAList wprog0) ∧
  ALL_DISTINCT (MAP FST wprog0) ∧
  s.stack = [] ∧
  t.code = fromAList wprog ∧
  lookup 0 t.locals = SOME (Loc 1 0) ∧
  t = s with code := t.code ∧
  s.code = fromAList wprog0 ⇒
  implements' T {semantics (t:(α,β,'ffi) wordSem$state) start}
              {semantics s start}
Proof
  strip_tac>>
  drule word_to_wordProofTheory.word_to_word_compile_semantics>>
  rpt (disch_then drule)>>
  disch_then (qspec_then ‘start’ assume_tac)>>
  gs[semanticsPropsTheory.implements'_def,
     semanticsPropsTheory.extend_with_resource_limit'_def]
QED

Theorem pan_to_word_state_rel_imp_semantics2:
  t.memory = mk_mem (make_funcs (compile_prog pan_code)) s.memory ∧
  distinct_params pan_code ∧
  consistent_labels s.memory pan_code ∧
  t.mdomain = s.memaddrs ∧ (t.be ⇔ s.be) ∧ t.ffi = s.ffi ∧
  ALOOKUP (fmap_to_alist t.store) CurrHeap = SOME (Word s.base_addr) ∧
  ALL_DISTINCT (MAP FST pan_code) ∧
  ALOOKUP pan_code start = SOME ([],prog) ∧
  lc < LENGTH pan_code ∧
  EL lc pan_code = (start,[],prog) ∧
  s.code = alist_to_fmap pan_code ∧
  t.code = fromAList (pan_to_word_compile_prog pan_code) ∧
  s.locals = FEMPTY ∧ size_of_eids pan_code < dimword (:α) ∧
  FDOM s.eshapes = FDOM ((get_eids pan_code):mlstring |-> 'a word) ∧
  lookup 0 t.locals = SOME (Loc 1 0) ⇒
  implements' T
              {semantics (t:(α,β,'ffi) wordSem$state) (lc + first_name)}
              {semantics (s:(α,'ffi) panSem$state) start}
Proof
  strip_tac>>
  drule pan_to_wordProofTheory.state_rel_imp_semantics>>
  rpt (disch_then drule)>>
  rpt strip_tac>>
  gs[semanticsPropsTheory.implements'_def,
     semanticsPropsTheory.extend_with_resource_limit'_def]
QED

(*** good_code for loop_to_word$comp ***)

Theorem comp_l_invariant:
  ∀ctxt prog l prog' l'. comp ctxt prog l = (prog',l') ⇒ FST l' = FST l
Proof
  ho_match_mp_tac loop_to_wordTheory.comp_ind >>
  rw[loop_to_wordTheory.comp_def] >>
  gvs[ELIM_UNCURRY,PULL_FORALL,AllCaseEqs()] >> metis_tac[PAIR]
QED

Theorem good_handlers_comp:
  ∀ctxt prog l. good_handlers (FST l) (FST (comp ctxt prog l))
Proof
  ho_match_mp_tac loop_to_wordTheory.comp_ind >>
  rw[wordPropsTheory.good_handlers_def,
     loop_to_wordTheory.comp_def] >>
  gvs[ELIM_UNCURRY] >>
  rpt(PURE_TOP_CASE_TAC >> gvs[]) >>
  metis_tac[PAIR,FST,SND,comp_l_invariant]
QED

Theorem loop_to_word_good_handlers:
  (loop_to_word$compile_prog prog) = prog' ⇒
  EVERY (λ(n,m,pp). good_handlers n pp) prog'
Proof
  fs[loop_to_wordTheory.compile_def,
     loop_to_wordTheory.compile_prog_def,
     loop_to_wordTheory.comp_func_def]>>
  rw[]>>
  fs[EVERY_MEM,MEM_MAP,PULL_EXISTS]>>
  PairCases >>
  rw[] >>
  pop_assum kall_tac >>
  rename1 ‘comp ctxt prog’ >>
  rename1 ‘(n,m)’ >>
  metis_tac[PAIR,FST,SND,good_handlers_comp]
QED

Theorem pan_to_word_good_handlers:
  pan_to_word$compile_prog prog = prog' ⇒
  EVERY (λ(n,m,pp). good_handlers n pp) prog'
Proof
  gs[pan_to_wordTheory.compile_prog_def,
     loop_to_wordTheory.compile_def]>>
  strip_tac>>
  irule loop_to_word_good_handlers>>metis_tac[]
QED

Theorem pan_to_lab_good_code_lemma:
  compile c.stack_conf c.data_conf lim1 lim2 offs stack_prog = code ∧
  compile asm_conf3 word_prog = (bm, wc, fs, stack_prog) ∧
  word_to_word$compile word_conf asm_conf3 word_prog0 = (col, word_prog) ∧
  compile_prog pan_prog = word_prog0 ∧
  stack_to_labProof$labels_ok code ∧
  all_enc_ok_pre conf code ⇒
  lab_to_targetProof$good_code conf LN code
Proof
  (* start of 'good_code' proof for initial compilation *)
  rw []
  \\ qmatch_asmsub_abbrev_tac `stack_to_labProof$labels_ok lab_prog`
  \\ fs[lab_to_targetProofTheory.good_code_def]
  \\ CONJ_TAC >- fs[Abbr `lab_prog`, stack_to_labTheory.compile_def]
  \\ CONJ_ASM1_TAC >- (
    fs [stack_to_labProofTheory.labels_ok_def]
    \\ qpat_x_assum `all_enc_ok_pre _ _` kall_tac
    \\ first_x_assum (fn t => mp_tac t \\ match_mp_tac EVERY_MONOTONIC)
    \\ simp[] \\ Cases \\ simp[]
    \\ metis_tac [labPropsTheory.EVERY_sec_label_ok]
  )
  \\ CONJ_TAC >- (
    fs [stack_to_labProofTheory.labels_ok_def]
    \\ qmatch_asmsub_abbrev_tac `ALL_DISTINCT (MAP ff _)`
    \\ `ff = Section_num` by
      (simp[Abbr`ff`,FUN_EQ_THM]>>Cases>>simp[])
    \\ fs [])
  \\ CONJ_TAC >- (
    fs [stack_to_labProofTheory.labels_ok_def]
    \\ first_x_assum (fn t => mp_tac t \\ match_mp_tac EVERY_MONOTONIC
      \\ simp[] \\ Cases \\ simp[] \\ NO_TAC)
  )
  \\ qpat_x_assum`Abbrev(lab_prog = _)` mp_tac
  \\ simp[markerTheory.Abbrev_def]
  \\disch_then (assume_tac o SYM)
  \\ drule stack_to_labProofTheory.stack_to_lab_stack_good_handler_labels
  \\ simp []
  \\ disch_then match_mp_tac
  \\ qmatch_asmsub_abbrev_tac ‘word_to_word$compile _ _ wprog’
  \\ pop_assum $ (assume_tac o GSYM o REWRITE_RULE [markerTheory.Abbrev_def])
  \\ drule pan_to_word_good_handlers
  \\ disch_tac
  \\ drule data_to_wordProofTheory.word_good_handlers_word_to_word
  \\ disch_then (qspecl_then [‘word_conf’, ‘asm_conf3’] assume_tac)
  \\ drule (INST_TYPE [beta|->alpha] word_to_stackProofTheory.word_to_stack_good_handler_labels)
  \\ strip_tac
  \\ pop_assum $ irule
  \\ simp []
  \\ qexists_tac ‘asm_conf3’>>gs[]
QED

(**** lab_pres for loop_to_word ****)

Theorem loop_to_word_comp_SND_LE:
  ∀ctxt prog l p r.
    comp ctxt prog l = (p,r) ⇒
    SND l ≤ SND r
Proof
  ho_match_mp_tac loop_to_wordTheory.comp_ind>>
  rw[loop_to_wordTheory.comp_def]>>
  rpt (FULL_CASE_TAC>>gs[])>>TRY (rveq>>gs[])>>
  pairarg_tac>>gs[]>>pairarg_tac>>gs[]>>
  rveq>>gs[]
QED

Theorem loop_to_word_comp_extract_labels_len:
  ∀ctxt prog l p r.
    comp ctxt prog l = (p,r) ⇒
    LENGTH (extract_labels p) = SND r - SND l
Proof
  ho_match_mp_tac loop_to_wordTheory.comp_ind>>
  rw[loop_to_wordTheory.comp_def]>>
  gs[wordPropsTheory.extract_labels_def]
  >- (
  pairarg_tac>>gs[]>>
  pairarg_tac>>gs[]>>
  rveq>>gs[wordPropsTheory.extract_labels_def]>>
  drule loop_to_word_comp_SND_LE>>strip_tac>>
  qpat_x_assum ‘_= (_, l')’ assume_tac>>
  drule loop_to_word_comp_SND_LE>>strip_tac>>
  gs[])
  >- (
  pairarg_tac>>gs[]>>
  pairarg_tac>>gs[]>>
  rveq>>gs[wordPropsTheory.extract_labels_def]>>
  drule loop_to_word_comp_SND_LE>>strip_tac>>
  qpat_x_assum ‘_= (_, l')’ assume_tac>>
  drule loop_to_word_comp_SND_LE>>strip_tac>>
  gs[])>>
  rpt (FULL_CASE_TAC>>gs[])>>
  rveq>>gs[wordPropsTheory.extract_labels_def]>>
  TRY (CASE_TAC>>gs[])>>
  pairarg_tac>>gs[]>>pairarg_tac>>gs[]>>
  rveq>>gs[wordPropsTheory.extract_labels_def]>>
  rpt (CASE_TAC>>gs[])>>
  drule loop_to_word_comp_SND_LE>>strip_tac>>gs[]>>
  qpat_x_assum ‘_= (_, (_, r))’ assume_tac>>
  drule loop_to_word_comp_SND_LE>>strip_tac>>gs[]
QED

Theorem loop_to_word_comp_extract_labels:
  ∀ctxt prog l p l'.
    loop_to_word$comp ctxt prog l = (p,l') ⇒
    EVERY (λ(q, r). q = FST l ∧ SND l ≤ r ∧ r < SND l') (extract_labels p)
Proof
  ho_match_mp_tac loop_to_wordTheory.comp_ind>>
  rw[loop_to_wordTheory.comp_def]>>
  gs[wordPropsTheory.extract_labels_def]
  >- (pairarg_tac>>gs[]>>
      pairarg_tac>>gs[]>>
      rveq>>gs[wordPropsTheory.extract_labels_def]>>
      ‘FST l'' = FST l’ by metis_tac[comp_l_invariant]>>gs[]>>
      drule loop_to_word_comp_SND_LE>>strip_tac>>
      qpat_x_assum ‘_= (_, l'')’ assume_tac>>
      drule loop_to_word_comp_SND_LE>>strip_tac>>
      conj_tac>>gs[EVERY_EL]>>strip_tac>>strip_tac>>pairarg_tac>>gs[]
      >- (first_x_assum $ qspec_then ‘n’ assume_tac>>gs[])>>
      last_x_assum $ qspec_then ‘n’ assume_tac>>gs[])
  >- (pairarg_tac>>gs[]>>
      pairarg_tac>>gs[]>>
      rveq>>gs[wordPropsTheory.extract_labels_def]>>
      ‘FST l'' = FST l’ by metis_tac[comp_l_invariant]>>gs[]>>
      drule loop_to_word_comp_SND_LE>>strip_tac>>
      qpat_x_assum ‘_= (_, l'')’ assume_tac>>
      drule loop_to_word_comp_SND_LE>>strip_tac>>
      conj_tac>>gs[EVERY_EL]>>strip_tac>>strip_tac>>pairarg_tac>>gs[]
      >- (first_x_assum $ qspec_then ‘n’ assume_tac>>gs[])>>
      last_x_assum $ qspec_then ‘n’ assume_tac>>gs[])>>
  rpt (FULL_CASE_TAC>>gs[])>>
  rveq>>gs[wordPropsTheory.extract_labels_def]>>
  TRY (CASE_TAC>>gs[])>>
  pairarg_tac>>gs[]>>
  pairarg_tac>>gs[]>>
  rveq>>gs[wordPropsTheory.extract_labels_def]>>
  rpt (CASE_TAC>>gs[])>>
  ‘q''' = FST l1’
    by (drule comp_l_invariant>>gs[])>>gs[]>>
  drule loop_to_word_comp_SND_LE>>strip_tac>>
  qpat_x_assum ‘_= (_, (_, r))’ assume_tac>>
  drule loop_to_word_comp_SND_LE>>strip_tac>>
  gs[]>>
  drule comp_l_invariant>>gs[]>>strip_tac>>
  conj_tac>>gs[EVERY_EL]>>strip_tac>>strip_tac>>pairarg_tac>>gs[]
  >- (last_x_assum $ qspec_then ‘n’ assume_tac>>gs[])>>
  first_x_assum $ qspec_then ‘n’ assume_tac>>gs[]
QED

Theorem loop_to_word_comp_ALL_DISTINCT:
  ∀ctxt prog l p r.
    comp ctxt prog l = (p,r) ⇒
    ALL_DISTINCT (extract_labels p)
Proof
  ho_match_mp_tac loop_to_wordTheory.comp_ind>>
  rw[loop_to_wordTheory.comp_def]>>
  gs[wordPropsTheory.extract_labels_def]
  >- (pairarg_tac>>gs[]>>
      pairarg_tac>>gs[]>>
      rveq>>
      gs[wordPropsTheory.extract_labels_def,
         ALL_DISTINCT_APPEND]>>rpt strip_tac>>
      drule loop_to_word_comp_extract_labels>>strip_tac>>
      drule loop_to_word_comp_SND_LE>>strip_tac>>
      qpat_x_assum ‘_= (_, l')’ assume_tac>>
      drule loop_to_word_comp_extract_labels>>strip_tac>>
      drule loop_to_word_comp_SND_LE>>strip_tac>>
      gs[EVERY_MEM]>>
      rpt (first_x_assum $ qspec_then ‘e’ assume_tac)>>gs[]>>
      Cases_on ‘e’>>gs[])
  >- (pairarg_tac>>gs[]>>
      pairarg_tac>>gs[]>>
      rveq>>
      gs[wordPropsTheory.extract_labels_def,
         ALL_DISTINCT_APPEND]>>rpt strip_tac>>
      drule loop_to_word_comp_extract_labels>>strip_tac>>
      drule loop_to_word_comp_SND_LE>>strip_tac>>
      qpat_x_assum ‘_= (_, l')’ assume_tac>>
      drule loop_to_word_comp_extract_labels>>strip_tac>>
      drule loop_to_word_comp_SND_LE>>strip_tac>>
      gs[EVERY_MEM]>>
      rpt (first_x_assum $ qspec_then ‘e’ assume_tac)>>gs[]>>
      Cases_on ‘e’>>gs[])>>
  rpt (FULL_CASE_TAC>>gs[])>>
  rveq>>gs[wordPropsTheory.extract_labels_def]>>
  TRY (CASE_TAC>>gs[])>>
  pairarg_tac>>gs[]>>
  pairarg_tac>>gs[]>>
  rveq>>gs[wordPropsTheory.extract_labels_def]>>
  rpt (CASE_TAC>>gs[])>>
  ‘q''' = FST l1’
    by (drule comp_l_invariant>>gs[])>>gs[]>>
  drule loop_to_word_comp_extract_labels>>strip_tac>>
  drule loop_to_word_comp_SND_LE>>strip_tac>>
  qpat_x_assum ‘_= (_, (_, r))’ assume_tac>>
  drule loop_to_word_comp_extract_labels>>strip_tac>>
  drule loop_to_word_comp_SND_LE>>strip_tac>>
  gs[]>>
  gs[ALL_DISTINCT_APPEND, EVERY_MEM]>>rw[]
  >- (first_x_assum $ qspec_then ‘(FST l1, r')’ assume_tac>>gs[])
  >- (last_x_assum $ qspec_then ‘(FST l1, r')’ assume_tac>>gs[])
  >- (first_x_assum $ qspec_then ‘(q, r)’ assume_tac>>gs[])
  >- (last_x_assum $ qspec_then ‘(q, r)’ assume_tac>>gs[])>>
  first_x_assum $ qspec_then ‘e’ assume_tac>>gs[]>>
  first_x_assum $ qspec_then ‘e’ assume_tac>>gs[]>>
  Cases_on ‘e’>>gs[]
QED

Theorem loop_to_word_comp_func_lab_pres:
    comp_func n' params body = p ⇒
    (∀n. n < LENGTH (extract_labels p) ⇒
         (λ(l1,l2). l1 = n' ∧ l2 ≠ 0 ∧ l2 ≠ 1)
         (EL n (extract_labels p))) ∧
    ALL_DISTINCT (extract_labels p)
Proof
  strip_tac>>
  gs[loop_to_wordTheory.comp_func_def]>>
  qmatch_asmsub_abbrev_tac ‘FST cmp = _’>>
  Cases_on ‘cmp’>>gs[]>>
  drule loop_to_word_comp_extract_labels>>strip_tac>>
  drule loop_to_word_comp_ALL_DISTINCT>>strip_tac>>
  gs[]>>rpt strip_tac>>
  gs[EVERY_EL]>>
  first_x_assum $ qspec_then ‘n’ assume_tac>>gs[]>>
  pairarg_tac>>gs[]
QED

Theorem loop_to_word_compile_prog_lab_pres:
  loop_to_word$compile_prog prog = prog' ⇒
  EVERY
  (λ(n,m,p).
     (let
        labs = extract_labels p
      in
        EVERY (λ(l1,l2). l1 = n ∧ l2 ≠ 0 ∧ l2 ≠ 1) labs ∧
        ALL_DISTINCT labs)) prog'
Proof
  strip_tac>>
  gs[loop_to_wordTheory.compile_prog_def]>>
  gs[EVERY_EL]>>ntac 2 strip_tac>>
  pairarg_tac>>gs[]>>rveq>>gs[EL_MAP]>>
  pairarg_tac>>gs[]>>
  drule loop_to_word_comp_func_lab_pres>>rw[]
QED

Theorem pan_to_word_compile_lab_pres:
  pan_to_word$compile_prog prog = prog' ⇒
  EVERY
  (λ(n,m,p).
     (let
        labs = extract_labels p
      in
        EVERY (λ(l1,l2). l1 = n ∧ l2 ≠ 0 ∧ l2 ≠ 1) labs ∧
        ALL_DISTINCT labs)) prog'
Proof
  strip_tac>>gs[pan_to_wordTheory.compile_prog_def]>>
  gs[loop_to_wordTheory.compile_def]>>
  drule loop_to_word_compile_prog_lab_pres>>gs[]
QED

Theorem pan_to_stack_compile_lab_pres:
  pan_to_word$compile_prog pan_code = wprog0 ∧
  word_to_word_compile c.word_to_word_conf mc.target.config wprog0 =(col,wprog) ∧
  word_to_stack_compile mc.target.config wprog = (bitmaps,c'',fs,p) ∧
  ALL_DISTINCT (MAP FST pan_code) ⇒
  ALL_DISTINCT (MAP FST p) ∧
  EVERY (λn. n ≠ 0 ∧ n ≠ 1 ∧ n ≠ 2 ∧ n ≠ gc_stub_location) (MAP FST p) ∧
  EVERY
  (λ(n,p).
     (let
        labs = extract_labels p
      in
        EVERY (λ(l1,l2). l1 = n ∧ l2 ≠ 0 ∧ l2 ≠ 1) labs ∧
        ALL_DISTINCT labs)) p
Proof
  strip_tac>>
  drule pan_to_word_compile_lab_pres>>strip_tac>>
  gs[]>>
  drule backendProofTheory.compile_to_word_conventions2>>
  strip_tac>>
  drule pan_to_wordProofTheory.first_compile_prog_all_distinct>>
  strip_tac>>gs[]>>
  ‘EVERY
   (λ(n,m,p).
      (let
         labs = extract_labels p
       in
         EVERY (λ(l1,l2). l1 = n ∧ l2 ≠ 0 ∧ l2 ≠ 1) labs ∧
         ALL_DISTINCT labs)) wprog’
    by (gs[EVERY2_EVERY]>>gs[EVERY_EL]>>ntac 2 strip_tac>>
        ntac 3 (first_x_assum $ qspec_then ‘n’ assume_tac)>>
        pairarg_tac>>gs[EL_ZIP, word_simpProofTheory.labels_rel_def]>>
        pairarg_tac>>gs[EL_MAP]>>strip_tac>>strip_tac>>
        ‘EL n (MAP FST wprog) = EL n (MAP FST wprog0)’ by rfs[]>>
        gs[EL_MAP]>>
        pairarg_tac>>gs[]>>
        ‘(l1, l2) ∈ set (extract_labels p'')’
          by (gs[MEM_SET_TO_LIST, SUBSET_DEF]>>
              first_assum irule>>metis_tac[MEM_EL])>>
        gs[MEM_EL]>>
        first_x_assum $ qspec_then ‘n''''’ assume_tac>>
        gs[]>>pairarg_tac>>gs[])>>
  drule (INST_TYPE [beta|->alpha] word_to_stackProofTheory.word_to_stack_compile_lab_pres)>>
  disch_then $ qspec_then ‘mc.target.config’ assume_tac>>
  drule_all pan_to_stack_first_ALL_DISTINCT>>
  strip_tac>>gs[]>>
  strip_tac>>gs[backend_commonTheory.stack_num_stubs_def]>>
  gs[backend_commonTheory.word_num_stubs_def,
     wordLangTheory.store_consts_stub_location_def,
     wordLangTheory.raise_stub_location_def,
     stackLangTheory.gc_stub_location_def,
     backend_commonTheory.stack_num_stubs_def]>>
  drule pan_to_word_compile_prog_lab_min>>
  gs[GSYM EVERY_MAP, EVERY_MEM]>>ntac 3 strip_tac>>
  first_x_assum $ qspec_then ‘n’ assume_tac>>gs[]
QED

(**)

Theorem loop_to_word_compile_prog_FST_eq:
  loop_to_word$compile_prog prog = prog' ⇒
  MAP FST prog' = MAP FST prog
Proof
  strip_tac>>gs[loop_to_wordTheory.compile_prog_def]>>
  ‘LENGTH prog = LENGTH prog'’ by (rveq>>gs[LENGTH_MAP])>>
  gs[MAP_EQ_EVERY2]>>gs[LIST_REL_EL_EQN]>>
  strip_tac>>strip_tac>>gs[]>>rveq>>gs[EL_MAP]>>
  pairarg_tac>>gs[]
QED

(* first_name offset *)

Theorem crep_to_loop_compile_prog_lab_min:
  crep_to_loop$compile_prog cprog = lprog ⇒
  EVERY (λprog. 60 ≤ FST prog) lprog
Proof
  gs[crep_to_loopTheory.compile_prog_def]>>
  gs[MAP2_MAP, EVERY_MEM]>>
  rpt strip_tac>>gvs[MEM_MAP,MEM_ZIP]>>
  pairarg_tac>>gs[crep_to_loopTheory.first_name_def]
QED

Theorem store_const_lab_min:
  x ≤ FST prog ∧
  EVERY (λp. x ≤ FST p) (SND prog) ∧
  store_cont s cont prog = (cont',prog') ⇒
  x ≤ FST prog' ∧ EVERY (λp. x ≤ FST p) (SND prog')
Proof
  strip_tac>>
  PairCases_on ‘prog’>>
  gs[loop_removeTheory.store_cont_def]>>
  rveq>>
  gs[EVERY_MEM]>>strip_tac>>strip_tac>>rveq>>gs[]
QED  
             
Theorem comp_with_loop_lab_min:
  comp_with_loop p p' cont prog = (q2, s')∧
  x ≤ FST prog ∧
  EVERY (λp. x ≤ FST p) (SND prog) ⇒
  (x ≤ FST s' ∧ EVERY (λp. x ≤ FST p) (SND s'))
Proof
  MAP_EVERY qid_spec_tac [‘s'’, ‘q2’, ‘prog’, ‘cont’, ‘p'’, ‘p’]>>
  recInduct loop_removeTheory.comp_with_loop_ind>>rw[]>>
  qpat_x_assum ‘comp_with_loop _ _ _ _ = _’ mp_tac>>
  rewrite_tac[loop_removeTheory.comp_with_loop_def]>>               
  strip_tac>>fs[]>>
  TRY (rpt (pairarg_tac>>fs[]))
  >- metis_tac[store_const_lab_min]
  >- metis_tac[store_const_lab_min]
  >- (Cases_on ‘handler’>>fs[]>>
      PairCases_on ‘x'’>>fs[]>>
      rpt (pairarg_tac>>fs[])>>
      metis_tac[store_const_lab_min])
  >- (Cases_on ‘handler’>>fs[]>>
      PairCases_on ‘x'’>>fs[]>>
      rpt (pairarg_tac>>fs[])>>
      metis_tac[store_const_lab_min])>>
  rveq>>gs[]>>
  drule_all store_const_lab_min>>
  strip_tac>>gs[]
QED

Theorem FOLDR_min:
  EVERY (λp. x ≤ FST p) prog ∧ prog ≠ [] ⇒
  x ≤ FOLDR MAX 0 (MAP FST prog)
Proof
  Induct_on ‘prog’>>gs[]
QED

Theorem loop_remove_comp_lab_min:
  FOLDR comp (m + 1,[]) prog = (n, prog') ∧
  (prog ≠ [] ⇒ x ≤ m) ∧
  EVERY (λp. x ≤ FST p) prog ⇒
  (prog ≠[] ⇒ x ≤ n) ∧ EVERY (λp. x ≤ FST p) prog'
Proof
  MAP_EVERY qid_spec_tac [‘n’, ‘m’, ‘prog'’, ‘prog’]>>
  Induct>>gs[]>>ntac 5 strip_tac>>
  PairCases_on ‘h’>>gs[loop_removeTheory.comp_def]>>
  pairarg_tac>>gs[]>>rveq>>gs[]>>
  drule comp_with_loop_lab_min>>
  disch_then $ qspec_then ‘x’ mp_tac>>
  qmatch_goalsub_abbrev_tac ‘FST xxx’>>
  Cases_on ‘xxx’>>gs[]>>
  first_x_assum $ qspecl_then [‘r’, ‘m’, ‘q’] assume_tac>>
  gs[]>>
  Cases_on ‘prog’>>gs[]
QED

Theorem loop_remove_comp_prog_lab_min:
  loop_remove$comp_prog prog = prog' ∧
  EVERY (λp. x ≤ FST p) prog ⇒
  EVERY (λp. x ≤ FST p) prog'
Proof
  gs[loop_removeTheory.comp_prog_def]>>strip_tac>>
  qmatch_asmsub_abbrev_tac ‘SND xxx’>>
  Cases_on ‘xxx’>>gs[]>>
  drule loop_remove_comp_lab_min>>
  disch_then $ qspec_then ‘x’ mp_tac>>gs[]>>
  impl_tac >-metis_tac[FOLDR_min]>>rw[]
QED

Theorem loop_to_word_compile_prog_lab_min:
  loop_to_word$compile_prog prog = prog' ∧
  EVERY (λp. x ≤ FST p) prog ⇒
  EVERY (λp. x ≤ FST p) prog'
Proof
  strip_tac>>
  drule loop_to_word_compile_prog_FST_eq>>gs[GSYM EVERY_MAP]
QED

Theorem loop_to_word_compile_lab_min:
  loop_to_word$compile prog = prog' ∧
  EVERY (λp. x ≤ FST p) prog ⇒
  EVERY (λp. x ≤ FST p) prog'
Proof
  strip_tac>>
  gs[loop_to_wordTheory.compile_def]>>
  drule_then irule loop_to_word_compile_prog_lab_min>>
  gs[]>>irule loop_remove_comp_prog_lab_min>>
  metis_tac[]
QED

Theorem pan_to_word_compile_prog_lab_min:
  pan_to_word_compile_prog pprog = wprog ⇒
  EVERY (λprog. 60 ≤ FST prog) wprog
Proof
  gs[pan_to_wordTheory.compile_prog_def]>>
  strip_tac>>
  drule_then irule loop_to_word_compile_lab_min>>
  irule crep_to_loop_compile_prog_lab_min>>metis_tac[]
QED

Theorem pan_to_stack_first_ALL_DISTINCT:
  pan_to_word_compile_prog pan_code = wprog0 ∧
  word_to_word_compile c.word_to_word_conf mc.target.config wprog0 = (col,wprog) ∧
  word_to_stack_compile mc.target.config wprog = (bitmaps,c'',fs,p) ∧
  ALL_DISTINCT (MAP FST pan_code) ⇒
  ALL_DISTINCT (MAP FST p)
Proof
  strip_tac>>drule_all pan_to_stack_compile_lab_pres>>gs[]
QED

Theorem pan_to_lab_labels_ok:
  pan_to_word_compile_prog pan_code = wprog0 ∧
  word_to_word_compile c.word_to_word_conf mc.target.config wprog0 = (col,wprog) ∧
  word_to_stack_compile mc.target.config wprog = (bitmaps,c'',fs,p) ∧
  stack_to_lab_compile c.stack_conf c.data_conf max_heap sp mc.target.config.addr_offset p = lprog ∧
  ALL_DISTINCT (MAP FST pan_code) ⇒
  labels_ok lprog
Proof
  strip_tac>>
  qpat_x_assum ‘_ = lprog’ (assume_tac o GSYM)>>gs[]>>
  irule stack_to_labProofTheory.stack_to_lab_compile_lab_pres>>
  drule_all pan_to_stack_compile_lab_pres>>gs[]
QED

(* inst_ok_less *)

Theorem full_imp_inst_ok_less:
  ∀c prog.
  full_inst_ok_less c prog ⇒
  every_inst (inst_ok_less c) prog
Proof
  recInduct wordPropsTheory.full_inst_ok_less_ind>>
  rw[wordPropsTheory.full_inst_ok_less_def,
     wordPropsTheory.inst_ok_less_def,
     wordPropsTheory.every_inst_def]>>
  rpt (CASE_TAC>>gs[])>>
QED

Theorem loop_to_word_comp_every_inst_ok_less:
  ∀ctxt prog l.
    byte_offset_ok c 0w ⇒
    every_inst (inst_ok_less c) (FST (comp ctxt prog l))
Proof
  ho_match_mp_tac loop_to_wordTheory.comp_ind >>
  rw[loop_to_wordTheory.comp_def,
    wordPropsTheory.every_inst_def,
    wordPropsTheory.inst_ok_less_def] >>
  gs[]>>TRY (rpt (CASE_TAC>>gs[]))>>
  TRY (rpt (pairarg_tac>>gs[]))>>
  gs[wordPropsTheory.every_inst_def]
QED        

Theorem loop_to_word_comp_func_every_inst_ok_less:
  loop_to_word$comp_func n params body = p ∧
  byte_offset_ok c 0w ⇒
  every_inst (inst_ok_less c) p
Proof
  strip_tac>>gs[loop_to_wordTheory.comp_func_def]>>
  rveq>>
  drule_then irule loop_to_word_comp_every_inst_ok_less
QED

Theorem loop_to_word_compile_prog_every_inst_ok_less:
  loop_to_word$compile_prog lprog = wprog0 ∧
  byte_offset_ok c 0w ⇒
  EVERY (λ(n,m,p). every_inst (inst_ok_less c) p) wprog0
Proof
  strip_tac>>gs[loop_to_wordTheory.compile_prog_def]>>
  rveq>>gs[EVERY_MAP, EVERY_EL]>>rpt strip_tac>>
  pairarg_tac>>gs[]>>
  pairarg_tac>>gs[]>>
  drule_then irule loop_to_word_comp_func_every_inst_ok_less>>
  gs[]
QED

Theorem loop_to_word_every_inst_ok_less:
  loop_to_word$compile lprog = wprog0 ∧
  byte_offset_ok c 0w ⇒
  EVERY (λ(n,m,p). every_inst (inst_ok_less c) p) wprog0
Proof
  strip_tac>>gs[loop_to_wordTheory.compile_def]>>
  drule_then irule loop_to_word_compile_prog_every_inst_ok_less>>
  gs[]
QED

Theorem pan_to_word_every_inst_ok_less:
  pan_to_word_compile_prog pan_code = wprog0 ∧
  byte_offset_ok c 0w ⇒
  EVERY (λ(n,m,p). every_inst (inst_ok_less c) p) wprog0
Proof
  gs[pan_to_wordTheory.compile_prog_def]>>strip_tac>>
  drule_then irule loop_to_word_every_inst_ok_less>>gs[]
QED

(** stack_to_lab$good_code **)

Theorem word_to_stack_compile_FST:
  word_to_stack_compile mc.target.config wprog = (bitmaps,c'',fs,p) ⇒
  MAP FST p =
  raise_stub_location::store_consts_stub_location::MAP FST wprog
Proof
  strip_tac>>gs[word_to_stackTheory.compile_def]>>
  pairarg_tac>>gs[]>>rveq>>gs[]>>
  drule_then irule word_to_stackProofTheory.MAP_FST_compile_word_to_stack
QED
  
Theorem word_to_stack_good_code_lemma:
  word_to_word_compile c.word_to_word_conf mc.target.config
          (pan_to_word_compile_prog pan_code) = (col,wprog) ∧
  word_to_stack_compile mc.target.config wprog = (bitmaps,c'',fs,p) ∧
  LENGTH mc.target.config.avoid_regs + 13 ≤ mc.target.config.reg_count ∧
         (* from backend_config_ok c *)
  ALL_DISTINCT (MAP FST pan_code) ⇒
  good_code (mc.target.config.reg_count −
           (LENGTH mc.target.config.avoid_regs + 3)) p
Proof
  gs[stack_to_labProofTheory.good_code_def]>>strip_tac>>
  qmatch_asmsub_abbrev_tac ‘word_to_word_compile _ _ wprog0 = _’>>
  qpat_x_assum ‘Abbrev (wprog0 = _)’ (assume_tac o GSYM o REWRITE_RULE [markerTheory.Abbrev_def])>>
  drule_all pan_to_stack_compile_lab_pres>>strip_tac>>gs[]>>
  drule backendProofTheory.compile_to_word_conventions2>>
  strip_tac>>
  drule pan_to_wordProofTheory.first_compile_prog_all_distinct>>
  strip_tac>>gs[]>>
  drule word_to_stack_compile_FST>>strip_tac>>
  drule word_to_stackProofTheory.word_to_stack_stack_convs>>
  gs[]>>impl_tac
  >- (gs[EVERY_EL]>>
      ntac 2 strip_tac>>
      ntac 3 (first_x_assum $ qspec_then ‘n’ assume_tac)>>
      gs[]>>
      pairarg_tac>>gs[]>>
      pairarg_tac>>gs[]>>simp[EL_MAP])>>
  strip_tac>>gs[backend_commonTheory.stack_num_stubs_def]>>
  gs[EVERY_EL]>>rpt strip_tac>>
  pairarg_tac>>gs[EL_MAP]>>
  qpat_x_assum ‘∀n. _ ⇒ alloc_arg _’ $ qspec_then ‘n’ assume_tac>>
  gs[]>>

  drule pan_to_word_compile_prog_lab_min>>
  gs[GSYM EVERY_MAP]>>
  qpat_x_assum ‘MAP FST _ = MAP FST _’ $ assume_tac o GSYM>>
  gs[]>>
  gs[GSYM EVERY_MAP, EVERY_MEM]>>strip_tac>>
  ‘MEM k (MAP FST p)’
    by (gs[MEM_MAP]>>gs[MEM_EL]>>gs[PULL_EXISTS]>>
        first_assum $ irule_at (Pos last)>>gs[])>>
  gs[backend_commonTheory.word_num_stubs_def,
     wordLangTheory.store_consts_stub_location_def,
     wordLangTheory.raise_stub_location_def,
     backend_commonTheory.stack_num_stubs_def]>>
  first_x_assum $ qspec_then ‘k’ assume_tac>>gs[]
QED

(** lab_to_target$good_code for compile_no_stubs **)

Theorem compile_no_stubs_sub_FST:
  MAP FST (compile c.reg_names
           (MAP (stack_remove_prog_comp c.jump offset sp)
            (MAP stack_alloc_prog_comp prog)))
  = MAP FST prog
Proof
  Induct_on ‘prog’>>fs[stack_removeTheory.prog_comp_def]
QED

(*
stack_to_targetProof$prog_to_section_labels_ok

*)

val MAP_prog_to_section_FST = Q.prove(`
  MAP (λs. case s of Section n v => n) (MAP prog_to_section prog) =
  MAP FST prog`,
      match_mp_tac LIST_EQ>>rw[EL_MAP]>>Cases_on`EL x prog`>>
      fs[stack_to_labTheory.prog_to_section_def]>>
  pairarg_tac>>fs[]);

val extract_label_store_list_code = Q.prove(`
  ∀a t ls.
  extract_labels (store_list_code a t ls) = []`,
  ho_match_mp_tac stack_removeTheory.store_list_code_ind>>
  EVAL_TAC>>fs[]);

Theorem stack_to_lab_compile_no_stubs_lab_pres:
  EVERY (λn. n ≠ 0 ∧ n ≠ 1 ∧ n ≠ 2 ∧ n ≠ gc_stub_location) (MAP FST prog) ∧
  EVERY (λn,p.
           let labs = extract_labels p in
             EVERY (λ(l1,l2).l1 = n ∧ l2 ≠ 0 ∧ l2 ≠ 1) labs ∧
             ALL_DISTINCT labs) prog ∧
  ALL_DISTINCT (MAP FST prog) ⇒
  labels_ok (compile_no_stubs c.reg_names c.jump offset sp prog)
Proof
  rw[stack_to_labProofTheory.labels_ok_def,
     stack_to_labTheory.compile_no_stubs_def]
  >- fs[MAP_prog_to_section_FST, compile_no_stubs_sub_FST]>>
  fs[EVERY_MAP,stack_to_labTheory.prog_to_section_def,
     EVERY_MEM,FORALL_PROD]>>
  rw[]>>pairarg_tac>>
  fs[labPropsTheory.extract_labels_def,
     labPropsTheory.extract_labels_append]>>
  Q.ISPECL_THEN [`T`,`p_2`,`p_1`,`next_lab p_2 2`] mp_tac stack_to_labProofTheory.stack_to_lab_lab_pres_T>>
  impl_keep_tac>-
   (*stack_names*)
   (fs[stack_namesTheory.compile_def,MEM_MAP]>>
    Cases_on`y` >>
    fs[stack_namesTheory.prog_comp_def,
       GSYM stack_namesProofTheory.stack_names_lab_pres]>>
    (*stack_remove*)
    qpat_x_assum ‘_ = stack_alloc_prog_comp _’ $ assume_tac o GSYM>>
    fs[]>>
    Cases_on`y'` >>
    fs[stack_removeTheory.prog_comp_def,
       GSYM stack_removeProofTheory.stack_remove_lab_pres]>>
    (*stack_alloc*)
    Cases_on ‘y''’>>
    fs[stack_allocTheory.prog_comp_def]>>
    Q.SPECL_THEN [`q''`,`next_lab r'' 2`,`r''`] mp_tac stack_allocProofTheory.stack_alloc_lab_pres>>
    fs [] >>
    impl_tac>-
     (rveq >> fs [stack_rawcallProofTheory.extract_labels_comp]>>
      res_tac>>fs[EVERY_MEM,FORALL_PROD]>>
      metis_tac[])>>
    rw[]>>pairarg_tac>>fs[])>>gs[]>>
  Cases_on `is_Seq p_2` THEN1
   (fs[EVERY_MEM]>>rw[]>>res_tac>>fs[ALL_DISTINCT_APPEND]
    >- (qsuff_tac`2 ≤ m` >> fs[]>>
        metis_tac[LESS_EQ_TRANS,
                  stack_to_labProofTheory.next_lab_non_zero])
    >> CCONTR_TAC>>fs[]>>res_tac>>fs[]
    >> imp_res_tac stack_allocProofTheory.extract_labels_next_lab>>fs[])
  >> fs [stack_to_labProofTheory.flatten_T_F]
  >> Q.ISPECL_THEN [`F`,`p_2`,`p_1`,`next_lab p_2 2`] mp_tac stack_to_labProofTheory.stack_to_lab_lab_pres
  >> impl_tac THEN1 fs []
  >> simp [] >> ntac 2 strip_tac

  >> rpt strip_tac >> fs [ALL_DISTINCT_APPEND]
  THEN1 (fs [EVERY_MEM] \\ res_tac \\ fs [])
  THEN1 (fs [EVERY_MEM] \\ res_tac \\ fs [])
  \\ CCONTR_TAC \\ fs [EVERY_MEM] \\ res_tac \\ fs []
QED

(*

    2.  word_to_word_compile c.word_to_word_conf mc.target.config wprog0 =
        (col,wprog)
    3.  word_to_stack_compile mc.target.config wprog = (bitmaps,c'',fs,p)
    9.  pan_to_word_compile_prog pan_code = wprog0
    4.  backend_config_ok c
    5.  mc_conf_ok mc
    6.  c.lab_conf.asm_conf = mc.target.config
    7.  ALL_DISTINCT (MAP FST pan_code)

   10.  labels_ok lprog
   12.  ALL_DISTINCT (MAP Section_num lprog)
   13.  EVERY (ALL_DISTINCT ∘ extract_labels ∘ Section_lines) lprog



   stack_to_lab_compile c.stack_conf c.data_conf max_heap sp
          mc.target.config.addr_offset p = lprog
    8.  noslang =
        compile_no_stubs c.stack_conf.reg_names c.stack_conf.jump
          mc.target.config.addr_offset sp p
   11.  EVERY sec_labels_ok lprog
   ------------------------------------
        EVERY sec_ends_with_label noslang ∧ EVERY sec_labels_ok noslang
   
*)

Theorem lab_to_target_no_stubs_good_code_lemma:
  compile c.lab_conf lprog = SOME (bytes,ltconf) ∧
  compile_no_stubs c.stack_conf.reg_names c.stack_conf.jump
                   mc.target.config.addr_offset sp p = noslang ∧
  stack_to_lab_compile c.stack_conf c.data_conf max_heap sp
                       mc.target.config.addr_offset p = lprog ∧
  word_to_word_compile c.word_to_word_conf mc.target.config
          (pan_to_word_compile_prog pan_code) = (col,wprog) ∧
  word_to_stack_compile mc.target.config wprog = (bitmaps,c'',fs,p) ∧
  backend_config_ok c ∧ mc_conf_ok mc ∧
  Abbrev (sp =  mc.target.config.reg_count −
             (LENGTH mc.target.config.avoid_regs + 3)) ∧
  c.lab_conf.asm_conf = mc.target.config ∧
  ALL_DISTINCT (MAP FST pan_code) ⇒
  good_code mc.target.config ltconf.labels noslang
Proof
  strip_tac>>gs[lab_to_targetProofTheory.good_code_def]>>
  qmatch_asmsub_abbrev_tac ‘word_to_word_compile _ _ wprog0 = _’>>
  qpat_x_assum ‘Abbrev (wprog0 = _)’ (assume_tac o GSYM o REWRITE_RULE [markerTheory.Abbrev_def])>>
  drule_all pan_to_stack_compile_lab_pres>>strip_tac>>
  drule_all pan_to_stack_first_ALL_DISTINCT>>strip_tac>>
  drule_all stack_to_lab_compile_no_stubs_lab_pres>>
  disch_then $ qspecl_then [‘sp’, ‘mc.target.config.addr_offset’, ‘c.stack_conf’] assume_tac>>
  gs[]>>
  drule stack_to_labProofTheory.labels_ok_imp>>strip_tac>>gs[]>>
  ‘EVERY sec_ends_with_label noslang’
    by (rveq>>gs[stack_to_labTheory.compile_no_stubs_def])>>
  gs[]>>

  conj_tac
  >- (gs[backendProofTheory.backend_config_ok_def,
         lab_to_targetProofTheory.mc_conf_ok_def]

  
cheat (* precondition *)>>
  conj_tac
  >- (irule SUBSET_TRANS>>
      irule_at Any stack_to_labProofTheory.stack_to_lab_stack_good_handler_labels_incr>>
      gs[]>>
      first_assum $ irule_at (Pos hd)>>
      irule (INST_TYPE [beta|->alpha] word_to_stackProofTheory.word_to_stack_good_handler_labels)>>
      first_assum $ irule_at (Pos hd)>>
      drule pan_to_word_good_handlers>>strip_tac>>
      drule data_to_wordProofTheory.word_good_handlers_word_to_word>>
      disch_then $ qspecl_then [‘c.word_to_word_conf’, ‘mc.target.config’] assume_tac>>
      gs[])>>
  (* all_enc_ok_pre *)
  ‘byte_offset_ok mc.target.config 0w’
    by (gs[lab_to_targetProofTheory.mc_conf_ok_def,
           backendProofTheory.backend_config_ok_def]>>
        drule good_dimindex_0w_8w>>gs[])>>
  gs[stack_to_labTheory.compile_no_stubs_def]>>rveq>>
  irule stack_to_labProofTheory.compile_all_enc_ok_pre>>gs[]>>
  irule stack_namesProofTheory.stack_names_stack_asm_ok>>
  conj_tac >-
   (gs[EVERY_MAP, EVERY_EL]>>rpt strip_tac>>
    pairarg_tac>>gs[]>>
    qmatch_asmsub_abbrev_tac ‘stack_remove_prog_comp _ _ _ aprog’>>
    Cases_on ‘aprog’>>gs[]>>
    gs[stack_removeTheory.prog_comp_def]>>
    rveq>>
    irule stack_removeProofTheory.stack_remove_comp_stack_asm_name>>
    gs[backendProofTheory.backend_config_ok_def,Abbr ‘sp’,
       lab_to_targetProofTheory.mc_conf_ok_def]>>
    gs[stackPropsTheory.reg_name_def]>>
    Cases_on ‘EL n p’>>gs[stack_allocTheory.prog_comp_def]>>
    rveq>>
    mp_tac (GEN_ALL stack_allocProofTheory.stack_alloc_comp_stack_asm_name)>>
    disch_then $ qspecl_then [‘mc.target.config’, ‘n'’, ‘next_lab r' 2’, ‘r'’] assume_tac>>
    gs[]>>pairarg_tac>>gs[]>>
    first_x_assum $ irule>>
    ‘EVERY (λ(n,p). stack_asm_name mc.target.config p ∧
                    stack_asm_remove mc.target.config p)
     (SND (SND (SND (word_to_stack_compile mc.target.config wprog))))’
      by (irule word_to_stackProofTheory.word_to_stack_stack_asm_convs>>
          gs[]>>
          drule backendProofTheory.compile_to_word_conventions2>>
          strip_tac>>gs[EVERY_EL]>>rpt strip_tac>>
          pairarg_tac>>gs[]>>
          first_x_assum $ qspec_then ‘n''’ assume_tac>>gs[]>>
          qmatch_asmsub_abbrev_tac ‘word_to_word_compile _ _ wprog0 = _’>>
          qpat_x_assum ‘Abbrev (wprog0 = _)’ (assume_tac o GSYM o REWRITE_RULE [markerTheory.Abbrev_def])>>
          drule pan_to_word_every_inst_ok_less>>gs[]>>
          disch_then $ qspec_then ‘mc.target.config’ assume_tac>>gs[]>>
          gs[EVERY_EL])>>
    gs[EVERY_EL]>>
    first_x_assum $ qspec_then ‘n’ assume_tac>>gs[])>>
  gs[backendProofTheory.backend_config_ok_def,
     lab_to_targetProofTheory.mc_conf_ok_def]
QED

Theorem good_dimindex_0w_8w:
  good_dimindex (:α) ⇒ (0w:α word) ≤ 8w ∧ -8w ≤ (0w:α word)
Proof
  strip_tac>>gs[]>>
  cheat
QED

(********)

Theorem pan_to_target_compile_semantics:
  pan_to_target$compile_prog c pan_code = SOME (bytes, bitmaps, c') ∧
  distinct_params pan_code ∧
  consistent_labels s.memory pan_code ∧
  ALL_DISTINCT (MAP FST pan_code) ∧
  lc < LENGTH pan_code ∧ EL lc pan_code = (start,[],prog) ∧
  InitGlobals_location = lc + first_name ∧
  s.code = alist_to_fmap pan_code ∧
  s.locals = FEMPTY ∧ size_of_eids pan_code < dimword (:α) ∧
  FDOM s.eshapes = FDOM ((get_eids pan_code):mlstring |-> 'a word) ∧
  backend_config_ok c ∧ lab_to_targetProof$mc_conf_ok mc ∧
  mc_init_ok c mc ∧
  s.ffi = ffi ∧ mc.target.config.big_endian = s.be ∧
  installed bytes cbspace bitmaps data_sp c'.lab_conf.ffi_names (heap_regs c.stack_conf.reg_names) mc ms ∧
  semantics s start ≠ Fail ⇒
  machine_sem (mc:(α,β,γ) machine_config) (ffi:'ffi ffi_state) ms ⊆
  extend_with_resource_limit {semantics (s:('a,'ffi) panSem$state) start}
Proof
  strip_tac>>
  last_x_assum mp_tac>>
  rewrite_tac[pan_to_targetTheory.compile_prog_def]>>
  rewrite_tac[backendTheory.from_word_def]>>
  rewrite_tac[backendTheory.from_stack_def]>>
  rewrite_tac[backendTheory.from_lab_def]>>
  strip_tac>>gs[]>>
  pairarg_tac>>gs[]>>
  pairarg_tac>>gs[]>>
  rename1 ‘_ = (col, wprog)’>>
  qmatch_asmsub_abbrev_tac ‘attach_bitmaps _ _ _ tprog = _’>>
  qmatch_asmsub_abbrev_tac ‘Abbrev (_ = compile _ lprog)’>>
  (* unfolding done *)

  drule backendProofTheory.compile_to_word_conventions2>>
  strip_tac>>
        
  (* apply lab_to_target *)
  (*  irule semanticsPropsTheory.implements'_trans>>*)
  irule SUBSET_TRANS>>
  irule_at Any (lab_to_targetProofTheory.semantics_compile |> REWRITE_RULE [semanticsPropsTheory.implements'_def, semanticsPropsTheory.extend_with_resource_limit'_def])>>

  (* instantiate / discharge *)
  qpat_assum ‘mc_conf_ok _’ $ irule_at Any>>
  qpat_x_assum ‘Abbrev (tprog = _)’ (assume_tac o GSYM o REWRITE_RULE[markerTheory.Abbrev_def])>>
  Cases_on ‘tprog’>>gs[backendTheory.attach_bitmaps_def]>>
  rename1 ‘compile _ _ = SOME x’>>Cases_on ‘x’>>
  rename1 ‘compile _ _ = SOME (tprog, ltconf)’>>
  first_assum $ irule_at Any>>
  qmatch_asmsub_abbrev_tac ‘installed _ _ _ _ _ hp _ _’>>
  Cases_on ‘hp’>>
  gs[targetSemTheory.installed_def]>>
  gs[backendProofTheory.mc_init_ok_def]>>
  gs[backendProofTheory.backend_config_ok_def]>>
  gs[backendTheory.attach_bitmaps_def]>>
  qpat_assum ‘good_init_state _ _ _ _ _ _ _ _ _’ $ irule_at Any>>
  ‘ltconf.ffi_names = SOME mc.ffi_names’
    by (rveq>>gs[])>>gs[]>>

  (* compiler_oracle_ok: for later *)
  qmatch_asmsub_abbrev_tac ‘stack_to_lab_compile _ _ max_heap sp _ _’>>
  qabbrev_tac ‘lorac = λn:num. (c'.lab_conf, p, [4w]:'a word list)’>>
  qabbrev_tac ‘sorac =
           (λn:num.
                (λ(c',p,b:'a word list).
                     (c',
                      compile_no_stubs c.stack_conf.reg_names
                        c.stack_conf.jump mc.target.config.addr_offset sp p))
                (lorac n))’>>
  qexists_tac ‘sorac’>>


  ‘compiler_oracle_ok sorac ltconf.labels (LENGTH bytes)
   mc.target.config mc.ffi_names’
   by (
    gs[lab_to_targetProofTheory.compiler_oracle_ok_def]>>
    gs[Abbr ‘sorac’, Abbr ‘lorac’]>>
    qmatch_goalsub_abbrev_tac ‘good_code _ _ noslang’>>
    ‘c'.lab_conf.labels = ltconf.labels ∧
     c'.lab_conf.pos = LENGTH bytes ∧
     c'.lab_conf.asm_conf = mc.target.config’
      by (gs[lab_to_targetTheory.compile_def]>>
          drule backendProofTheory.compile_lab_lab_conf>>
          strip_tac>>gs[]>>
          drule backendProofTheory.compile_lab_LENGTH>>
          strip_tac>>gs[]>>
          rveq>>gs[])>>gs[]>>
            (* good_code mc.target.config c'.lab_conf.labels
          (compile_no_stubs c.stack_conf.reg_names c.stack_conf.jump
             mc.target.config.addr_offset sp p

             need to look into compile_no_stubs *)
                                                                        
(*
backendProofTheory.compile_lab_domain_labels (THEOREM)
------------------------------------------------------
⊢ compile_lab c prog = SOME (b,c') ⇒
  domain c'.labels = IMAGE FST (get_code_labels prog) ∪ domain c.labels

*)
    cheat)>>gs[]>>
        
  conj_tac >- ( (* good_code mc.target.config LN lprog*)
      irule (INST_TYPE [beta|->alpha] pan_to_lab_good_code_lemma)>>
      gs[]>>
      rpt (first_assum $ irule_at Any)>>
      qpat_x_assum ‘Abbrev (lprog = _)’ (assume_tac o GSYM o REWRITE_RULE [markerTheory.Abbrev_def])>>
      first_assum $ irule_at Any>>
      qmatch_asmsub_abbrev_tac ‘word_to_word_compile _ _ wprog0 = _’>>
      qpat_x_assum ‘Abbrev (wprog0 = _)’ (assume_tac o GSYM o REWRITE_RULE [markerTheory.Abbrev_def])>>
      (* labels_ok *)
      drule_all pan_to_lab_labels_ok>>strip_tac>>gs[]>>
      (* all_enc_ok_pre mc.target.config lprog *)
      ‘byte_offset_ok mc.target.config 0w’
        by (gs[lab_to_targetProofTheory.mc_conf_ok_def]>>
            drule good_dimindex_0w_8w>>gs[])>>
      gs[stack_to_labTheory.compile_def]>>rveq>>
      irule stack_to_labProofTheory.compile_all_enc_ok_pre>>
      conj_tac >-
       (irule stack_namesProofTheory.stack_names_stack_asm_ok>>
        gs[]>>
        irule stack_removeProofTheory.stack_remove_stack_asm_name>>
        gs[lab_to_targetProofTheory.mc_conf_ok_def]>>
        gs[stackPropsTheory.reg_name_def, Abbr ‘sp’]>>
        irule stack_allocProofTheory.stack_alloc_stack_asm_convs>>
        gs[stackPropsTheory.reg_name_def]>>
        assume_tac (GEN_ALL stack_rawcallProofTheory.stack_alloc_stack_asm_convs)>>
        first_x_assum (qspecl_then [‘p’, ‘mc.target.config’] assume_tac)>>gs[]>>
        (* reshaping... *)
        gs[GSYM EVERY_CONJ]>>
        ‘∀x. (λ(n:num,p). stack_asm_name mc.target.config p ∧
                          stack_asm_remove mc.target.config p) x ⇒
             (λx. (λ(n,p). stack_asm_name mc.target.config p) x ∧
                  (λ(n,p). stack_asm_remove mc.target.config p) x) x’
          by (rw[]>>pairarg_tac>>gs[])>>
        drule_then irule EVERY_MONOTONIC>>
        ‘p = SND (SND (SND (word_to_stack_compile mc.target.config wprog)))’ by gs[]>>
        pop_assum $ (fn h => rewrite_tac[h])>>
        irule word_to_stackProofTheory.word_to_stack_stack_asm_convs>>
        gs[]>>
        irule EVERY_MONOTONIC>>
        qpat_assum ‘EVERY _ wprog’ $ irule_at Any>>
        rpt strip_tac>>pairarg_tac>>gs[]>>
        first_x_assum $ irule>>
        irule pan_to_word_every_inst_ok_less>>metis_tac[])>>
      gs[])>>

  (* lab_to_stack *)
  qmatch_goalsub_abbrev_tac ‘labSem$semantics labst’>>
  mp_tac (GEN_ALL stack_to_labProofTheory.full_make_init_semantics |> INST_TYPE [beta|-> “:α lab_to_target$config”, gamma|-> “:'ffi”])>>

  (* instantiate / discharge *)
  
  gs[lab_to_targetProofTheory.mc_conf_ok_def]>>
  disch_then (qspec_then ‘labst’ mp_tac)>>gs[]>>
  ‘labst.code = stack_to_lab_compile c.stack_conf c.data_conf
                                     (2 * max_heap_limit (:α) c.data_conf − 1)
                                     (mc.target.config.reg_count −
                                      (LENGTH mc.target.config.avoid_regs + 3))
                                     mc.target.config.addr_offset p’
    by gs[Abbr ‘labst’, Abbr ‘lprog’,
          lab_to_targetProofTheory.make_init_def]>>
  disch_then $ drule_at Any>>
  qabbrev_tac ‘sopt = full_make_init c.stack_conf c.data_conf max_heap sp mc.target.config.addr_offset bitmaps p labst
             (set mc.callee_saved_regs) data_sp lorac’>>
  Cases_on ‘sopt’>>gs[]>>
  rename1 ‘_ = (sst, opt)’>>
  disch_then $ drule_at (Pos hd)>>
  ‘labst.compile_oracle =
                         (λn.
                (λ(c',p,b).
                     (c',
                      compile_no_stubs c.stack_conf.reg_names
                        c.stack_conf.jump mc.target.config.addr_offset sp p))
                  (lorac n))’
    by gs[Abbr ‘labst’, Abbr ‘sorac’,
          lab_to_targetProofTheory.make_init_def]>>
  rpt (disch_then $ drule_at Any)>>
  ‘ ¬MEM labst.link_reg mc.callee_saved_regs ∧ labst.pc = 0 ∧
           (∀k i n. MEM k mc.callee_saved_regs ⇒ labst.io_regs n i k = NONE) ∧
           (∀k n. MEM k mc.callee_saved_regs ⇒ labst.cc_regs n k = NONE) ∧
           (∀x. x ∈ labst.mem_domain ⇒ w2n x MOD (dimindex (:α) DIV 8) = 0) ∧
           good_code sp p ∧ (∀n. good_code sp (FST (SND (lorac n)))) ∧
           10 ≤ sp ∧
           (MEM (find_name c.stack_conf.reg_names (sp + 1))
              mc.callee_saved_regs ∧
            MEM (find_name c.stack_conf.reg_names (sp + 2))
              mc.callee_saved_regs) ∧ mc.len2_reg = labst.len2_reg ∧
           mc.ptr2_reg = labst.ptr2_reg ∧ mc.len_reg = labst.len_reg ∧
           mc.ptr_reg = labst.ptr_reg ∧
           (case mc.target.config.link_reg of NONE => 0 | SOME n => n) =
           labst.link_reg ∧ ¬labst.failed’
  by (gs[Abbr ‘labst’, Abbr ‘sp’,
         lab_to_targetProofTheory.make_init_def]>>
      gs[Abbr ‘lorac’]>>
      drule backendProofTheory.byte_aligned_MOD>>gs[]>>
      strip_tac>>
      drule_all word_to_stack_good_code_lemma>>
      rw[])>>
     gs[]>>
  (* LENGTH mc.target.config.avoid_regs + 13 ≤ mc.target.config.reg_count*)
  
  ‘memory_assumption c.stack_conf.reg_names bitmaps data_sp labst’
    by (
    gs[stack_to_labProofTheory.memory_assumption_def]>>
    qpat_assum ‘Abbrev (labst = _)’ mp_tac>>
    rewrite_tac[markerTheory.Abbrev_def]>>
    rewrite_tac[lab_to_targetProofTheory.make_init_def,
       labSemTheory.state_component_equality]>>
    simp[]>>strip_tac>>gs[]>>
    gs[backendProofTheory.heap_regs_def]>>

    rewrite_tac[Once INTER_COMM]>>
    rewrite_tac[UNION_OVER_INTER]>>
    rewrite_tac[Once UNION_COMM]>>
    irule miscTheory.fun2set_disjoint_union>>
    gs[]>>
    conj_tac >- (
      irule backendProofTheory.word_list_exists_imp>>
      gs[]>>
      conj_tac >- (
        gs[byteTheory.bytes_in_word_def]>>

               blastLib.BBLAST_TAC
(*  dimindex (:α) DIV 8 *
        (w2n (-1w * t.regs q + t.regs r) DIV w2n bytes_in_word) <
        dimword (:α) *)
        cheat)>>

      rewrite_tac[SET_EQ_SUBSET]>>
      rw[]>- (
        gs[SUBSET_DEF]>>strip_tac>>strip_tac>>
(* x ∈
        addresses (t.regs mc.len_reg)
          (w2n (t.regs mc.len2_reg + -1w * t.regs mc.len_reg) DIV
           w2n bytes_in_word)*)
        cheat)
      >- (
        rewrite_tac[stack_removeProofTheory.addresses_thm]>>
        rewrite_tac[SUBSET_DEF]>>strip_tac>>strip_tac>>
        gs[IN_GSPEC_IFF]>>
        rewrite_tac[IN_APP]>>
        irule alignmentTheory.byte_aligned_add>>
        gs[data_to_word_assignProofTheory.byte_aligned_bytes_in_word])>>

      rewrite_tac[stack_removeProofTheory.addresses_thm]>>
      rewrite_tac[SUBSET_DEF]>>strip_tac>>strip_tac>>
      gs[IN_GSPEC_IFF]>>
      ‘0 < w2n bytes_in_word’
        by gs[labPropsTheory.good_dimindex_def,
              byteTheory.bytes_in_word_def,
              wordsTheory.dimword_def]>>
      drule_all (iffLR X_LT_DIV)>>strip_tac>>
      rw[]
      >- (
        rewrite_tac[WORD_LS]>>
        gs[targetSemTheory.good_init_state_def]>>
(*   w2n (t.regs mc.len_reg) ≤
        w2n (t.regs mc.len_reg + bytes_in_word * n2w i) *)
        cheat)
      >- (gs[]>>
(* t.regs mc.len_reg + bytes_in_word * n2w i <₊ t.regs mc.len2_reg *)
          cheat)>>
    irule DISJOINT_INTER>>gs[DISJOINT_SYM])>>
  gs[]>>

  (* apply stack_to_lab *)
  strip_tac>>
  ‘semantics InitGlobals_location sst ≠ Fail ⇒
   semantics labst ≠ Fail’ by rw[]>>
  pop_assum $ irule_at Any>>
        
  (*  irule semanticsPropsTheory.implements'_trans>>*)
  irule_at Any $ METIS_PROVE [] “∀x y z. x = y ∧ y ∈ z ⇒ x ∈ z”>>
    pop_assum $ irule_at Any>>
                
    



  (* word_to_stack *)

  (* instantiate / discharge *)
  ‘FST (word_to_stack_compile mc.target.config wprog) ≼ sst.bitmaps ∧
  sst.code = fromAList p’
    by (
    gs[stack_to_labProofTheory.full_make_init_def]>>
    gs[stack_removeProofTheory.make_init_opt_def]>>
    Cases_on ‘opt’>>gs[]>>
    gs[stack_removeProofTheory.make_init_any_def,
       stack_allocProofTheory.make_init_def,
       stack_to_labProofTheory.make_init_def,
       stack_namesProofTheory.make_init_def]>>
    qmatch_asmsub_abbrev_tac ‘evaluate (init_code gengc _ _, s')’>>
    qmatch_asmsub_abbrev_tac ‘make_init_opt _ _ _ _ coracle jump off _ code _’>>
    Cases_on ‘evaluate (init_code gengc max_heap sp, s')’>>gs[]>>
    rename1 ‘evaluate _ = (q', r')’>>
    Cases_on ‘q'’>>gs[]>>rveq>>
    gs[stackSemTheory.state_component_equality]>>
    Cases_on ‘make_init_opt gengc max_heap bitmaps data_sp coracle jump off sp code s'’>>
    gs[stackSemTheory.state_component_equality]>>
    gs[stack_removeProofTheory.make_init_opt_def]>>
    gs[stack_removeProofTheory.init_reduce_def]>>    
    gs[stack_removeProofTheory.init_prop_def]>>
    rveq>>gs[stackSemTheory.state_component_equality])>>

  drule_at Any word_to_stackProofTheory.compile_semantics>>
  gs[]>>
  ‘EVERY (λ(n,m,prog).
            flat_exp_conventions prog ∧
            post_alloc_conventions
            (mc.target.config.reg_count −
             (LENGTH mc.target.config.avoid_regs + 5)) prog) wprog’
  by (qpat_x_assum ‘EVERY _ wprog’ assume_tac>>
      gs[EVERY_EL]>>rpt strip_tac>>
      first_x_assum $ qspec_then ‘n’ assume_tac>>
      pairarg_tac>>gs[])>>gs[]>>
  disch_then (qspec_then ‘InitGlobals_location’ mp_tac)>>
  disch_then (qspec_then ‘λn. ((1, c'.lab_conf), wprog)’ mp_tac)>>   (* later *)

  qmatch_goalsub_abbrev_tac ‘init_state_ok _ _ worac’>>
  ‘¬ NULL bitmaps ∧ HD bitmaps = 4w’
    by (drule word_to_stackProofTheory.compile_word_to_stack_bitmaps>>
        strip_tac>>Cases_on ‘bitmaps’>>gs[])>>
  ‘init_state_ok
           (mc.target.config.reg_count −
            (LENGTH mc.target.config.avoid_regs + 5)) sst worac ∧
         ALOOKUP wprog raise_stub_location = NONE ∧
         ALOOKUP wprog store_consts_stub_location = NONE’
    by (
      

       
      (**********)
      (*
qpat_assum ‘word_to_stack$compile _ _ = _’ $ assume_tac o REWRITE_RULE[word_to_stackTheory.compile_def]>>
        gs[]>>
        pairarg_tac>>gs[]>>

        drule word_to_stackProofTheory.MAP_FST_compile_word_to_stack>>
        strip_tac>>
        pairarg_tac>>gs[]>>
*)

conj_tac >- (
      irule stack_to_labProofTheory.IMP_init_state_ok>>
      gs[]>>
      Cases_on ‘opt’>>gs[]>>rename1 ‘(sst, SOME xxx)’>>
      MAP_EVERY qexists_tac [‘data_sp’, ‘c.data_conf’, ‘labst’, ‘max_heap’, ‘p’, ‘set mc.callee_saved_regs’, ‘c.stack_conf’, ‘sp’, ‘mc.target.config.addr_offset’, ‘TL bitmaps’, ‘xxx’]>>

      conj_tac >-
       (strip_tac>>gs[Abbr ‘worac’]>>
        rewrite_tac[CONJ_ASSOC]>>conj_tac
        >- (
         gs[EVERY_EL]>>
         gs[GSYM FORALL_AND_THM]>>gs[GSYM IMP_CONJ_THM]>>
         ntac 2 strip_tac>>
         first_x_assum $ qspec_then ‘n’ assume_tac>>
         pairarg_tac>>gs[]>>
         
         qmatch_asmsub_abbrev_tac ‘word_to_word_compile _ _ wprog0 = _’>>
         qpat_x_assum ‘Abbrev (wprog0 = _)’ (assume_tac o GSYM o REWRITE_RULE [markerTheory.Abbrev_def])>>
         drule pan_to_word_compile_prog_lab_min>>
         strip_tac>>
         ‘EL n (MAP FST wprog0) = EL n (MAP FST wprog)’
           by gs[]>>
         gs[EL_MAP, EVERY_EL]>>
         first_x_assum $ qspec_then ‘n’ assume_tac>>
         ‘LENGTH wprog0 = LENGTH wprog’ by metis_tac[LENGTH_MAP]>>
         gs[wordLangTheory.raise_stub_location_def, EL_MAP,
            wordLangTheory.store_consts_stub_location_def]>>
         gs[backend_commonTheory.word_num_stubs_def]>>
         gs[backend_commonTheory.stack_num_stubs_def])>>
        strip_tac>>
(*
n = 0
   ------------------------------------
        TL bitmaps = []
        *)
        cheat)>>
      qpat_assum ‘HD _ = _’ $ (fn th => rewrite_tac[th]) o GSYM>>
      gs[CONS]>>gs[Abbr ‘worac’, Abbr ‘lorac’]>>
      pairarg_tac>>gs[]>>
      

            gs[word_to_stackTheory.compile_def]>>
            pairarg_tac>>gs[]>>
(* oracle mismatch *)
            pairarg_tac>>gs[]>>
      Cases_on ‘wprog’>>gs[]
      >- gs[word_to_stackTheory.compile_word_to_stack_def]
      

      drule word_to_stackProofTheory.compile_word_to_stack_bitmaps>>

            rveq
                
            
(*

 lorac = (λn.
               (λ((bm0,cfg),progs).
                    (λ(progs,fs,bm). (cfg,progs,append (FST bm)))
                      (compile_word_to_stack
                         (mc.target.config.reg_count −
                          (LENGTH mc.target.config.avoid_regs + 5)) progs
                         (Nil,bm0))) (worac n))


lorac = (λn. (c'.lab_conf,p,[]))

equally:
   115.  worac n = ((bm0,cfg),progs)
   116.  compile_word_to_stack
           (mc.target.config.reg_count −
            (LENGTH mc.target.config.avoid_regs + 5)) progs (Nil,bm0) =
         (progs',fs',bm')
      
bm0 = 1
cfg = c'.lab_conf
progs = wprog

List [4w] instead of []

           
actual:
 compile_word_to_stack
           (mc.target.config.reg_count −
            (LENGTH mc.target.config.avoid_regs + 5)) wprog (List [4w],1) =
         (progs'',fs'',bitmaps')
         
      
*)                

        gs[EVERY_CONJ]
      pairarg_tac>>gs[]>>h
      
    


    cheat)>>cheat)>> (* repeat of the end of init_state_ok *)
gs[]>>

  (* apply word_to_stack *)
  qmatch_goalsub_abbrev_tac ‘wordSem$semantics wst _’>>
  strip_tac>>
  gs[semanticsPropsTheory.extend_with_resource_limit'_def]>>
  ‘semantics wst InitGlobals_location ≠ Fail ⇒
   semantics InitGlobals_location sst ∈
   extend_with_resource_limit {semantics wst InitGlobals_location}’
    by (Cases_on ‘word_lang_safe_for_space wst InitGlobals_location’>>
        gs[semanticsPropsTheory.extend_with_resource_limit_def])>>
    gs[semanticsPropsTheory.extend_with_resource_limit'_def]>>

  (* elim stackSem ≠ Fail *)
  ‘semantics wst InitGlobals_location ≠ Fail ⇒
   semantics InitGlobals_location sst ≠ Fail’
    by (rw[]>>
        gs[semanticsPropsTheory.extend_with_resource_limit_def])>>

  pop_assum $ irule_at Any>>


(*     
  mp_tac (GEN_ALL word_to_stackProofTheory.compile_semantics |> INST_TYPE [gamma|-> “:'a lab_to_target$config”, beta|->alpha])>>
  *)

  (* apply word_to_stack *)
  irule_at Any $ METIS_PROVE [] “∀x y z f. x = y ∧ z ∈ f x ⇒ z ∈ f y” >>
  pop_assum $ irule_at Any>>gs[]>>

  (* word_to_word *)
  drule (word_to_wordProofTheory.word_to_word_compile_semantics |> INST_TYPE [beta |-> “: num # 'a lab_to_target$config”])>>

  (* instantiate / discharge *)
  disch_then (qspecl_then [‘wst’, ‘InitGlobals_location’, ‘wst with code := fromAList (pan_to_word_compile_prog pan_code)’] mp_tac)>>
  gs[]>>
  ‘gc_fun_const_ok wst.gc_fun ∧
   no_install_code (fromAList (pan_to_word_compile_prog pan_code)) ∧
   no_alloc_code (fromAList (pan_to_word_compile_prog pan_code)) ∧
   no_mt_code (fromAList (pan_to_word_compile_prog pan_code))’
    by (conj_tac >- (
         gs[Abbr ‘wst’, word_to_stackProofTheory.make_init_def]>>
         gs[stack_to_labProofTheory.full_make_init_def,
            stack_removeProofTheory.make_init_opt_def]>>
         Cases_on ‘opt’>>gs[]>>
         gs[stack_removeProofTheory.make_init_any_def,
            stack_allocProofTheory.make_init_def,
            stack_to_labProofTheory.make_init_def,
            stack_namesProofTheory.make_init_def]>>
         rveq>>
         gs[stackSemTheory.state_component_equality]>>
         irule data_to_word_gcProofTheory.gc_fun_const_ok_word_gc_fun)>>
        conj_tac >- (
         irule pan_to_word_compile_prog_no_install_code>>
         metis_tac[])>>
        conj_tac >- (
         irule pan_to_word_compile_prog_no_alloc_code>>
         metis_tac[])>>
        irule pan_to_word_compile_prog_no_mt_code>>
        metis_tac[])>>gs[]>>
  ‘ALL_DISTINCT (MAP FST (pan_to_word_compile_prog pan_code)) ∧
         wst.stack = [] ∧ wst.code = fromAList wprog ∧
         lookup 0 wst.locals = SOME (Loc 1 0) ∧
         wst = wst with code := wst.code’
    by (
    drule pan_to_wordProofTheory.first_compile_prog_all_distinct>>
    strip_tac>>
    gs[Abbr ‘wst’, word_to_stackProofTheory.make_init_def])>>gs[]>>

  (* remove wordSem1 ≠ Fail *)
  qmatch_goalsub_abbrev_tac ‘fromAList wprog0’>>
  strip_tac>>
  qmatch_asmsub_abbrev_tac ‘semantics wst0 _ ≠ Fail’>>
  ‘semantics wst0 InitGlobals_location ≠ Fail ⇒
   semantics wst InitGlobals_location ≠ Fail’
    by (rw[]>>gs[])>>
  pop_assum $ irule_at Any>>
  
  (* apply word_to_word *)
  irule_at Any EQ_TRANS>>
  qpat_x_assum ‘_ ≠ Fail ⇒ _ = _’ $ (irule_at Any) o GSYM>>
  gs[]>>rewrite_tac[Once CONJ_COMM]>>
  gs[GSYM CONJ_ASSOC]>>

  (* pan_to_word *)
  qpat_x_assum ‘lc + _ = _’ (SUBST_ALL_TAC o GSYM)>>
  ‘wst0.code = fromAList (pan_to_word_compile_prog pan_code)’
  by gs[Abbr ‘wst0’, wordSemTheory.state_component_equality]>>
  drule_at (Pos (el 15)) (INST_TYPE [beta|-> “:num # α lab_to_target$config”] pan_to_wordProofTheory.state_rel_imp_semantics)>>
  gs[]>>
    rpt $ disch_then $ drule_at Any>>
  impl_tac >- (
  qpat_x_assum ‘_ ≠ Fail ⇒ _ ∈ _’ kall_tac>>
  gs[Abbr ‘wst’, Abbr ‘wst0’,
     word_to_stackProofTheory.make_init_def]>>
  drule_all ALOOKUP_ALL_DISTINCT_EL>>strip_tac>>gs[]>>
  gs[word_to_stackProofTheory.init_state_ok_def]>>
  gs[stack_to_labProofTheory.full_make_init_def,
     stack_removeProofTheory.make_init_opt_def]>>

  Cases_on ‘opt’>>gs[]>>
  gs[stack_removeProofTheory.make_init_any_def,
    stack_allocProofTheory.make_init_def,
    stack_to_labProofTheory.make_init_def,
    stack_namesProofTheory.make_init_def]>>
  qmatch_asmsub_abbrev_tac ‘evaluate (init_code gengc _ _, s')’>>
  qmatch_asmsub_abbrev_tac ‘make_init_opt _ _ _ _ coracle jump off _ code _’>>
  Cases_on ‘evaluate (init_code gengc max_heap sp, s')’>>gs[]>>
  rename1 ‘evaluate _ = (q', r')’>>
  Cases_on ‘q'’>>gs[]>>
  Cases_on ‘make_init_opt gengc max_heap bitmaps sp coracle jump off sp code s'’>>gs[]>>
  
  cheat>>
(*  gs[stack_removeProofTheory.make_init_opt_def]>>
  gs[stack_removeProofTheory.init_prop_def]>>
  gs[stack_removeProofTheory.init_reduce_def]>>



  gs[stack_removeProofTheory.init_prop_def]>>
  rveq>>gs[stackSemTheory.state_component_equality]>>
  gs[wordSemTheory.isWord_def, wordSemTheory.theWord_def]>>
  gs[flookup_fupdate_list]>>
  gs[ALOOKUP_APPEND]>>
  gs[stack_removeTheory.store_init_def]>>
  gs[APPLY_UPDATE_LIST_ALOOKUP]>>
  gs[ALOOKUP_def]>>
  gs[stack_removeTheory.store_list_def]>>

*)
  ‘init_pre gengc max_heap bitmaps sp sp InitGlobals_location s'’
    by (
cheat

    (*gs[stack_removeProofTheory.init_pre_def,
           Abbr ‘s'’]>>
        gs[stack_removeTheory.compile_def]>>
        conj_tac >-
         gs[lookup_fromAList, stack_removeTheory.init_stubs_def]>>
        gs[stack_removeProofTheory.init_code_pre_def]>>
        gs[stack_removeTheory.init_stubs_def,
          domain_fromAList]>>
        gs[Abbr ‘sp’]>>gs[PULL_EXISTS]>>
        qmatch_asmsub_abbrev_tac ‘evaluate (init_code _ _ sp, s')’>>
        Cases_on ‘evaluate (init_code gengc max_heap sp, s')’>>gs[]>>
        rename1 ‘evaluate _ = (q', r')’>>
        Cases_on ‘q'’>>gs[]>>rveq>>
        gs[stack_removeProofTheory.init_reduce_def]>>
        gs[stack_removeProofTheory.init_prop_def]>>
        gs[stack_removeTheory.store_init_def]>>
gs[flookup_thm]>>
        gs[FUPDATE_LIST,FUPDATE_DEF]>>
        gs[FOLDL]


        gs[LINV_LO]>>
        gs[FLOOKUP_MAP_KEYS_MAPPED]>>
                
     *)

drule stack_removeProofTheory.evaluate_init_code>>
         
disch_then (qspecl_then [‘off’, ‘jump’, ‘coracle’, ‘code’] mp_tac)>>
impl_tac >- (
      gs[Abbr ‘s'’]>>
      conj_tac >- (
        gs[Abbr ‘coracle’]>>
        gs[MEM_EL, PULL_EXISTS]>>cheat)>>
      conj_tac >- (
        gs[stack_removeTheory.compile_def]>>
        gs[stack_removeTheory.init_stubs_def,
           stack_removeTheory.stack_err_lab_def,
           lookup_fromAList])>>
      gs[stack_removeProofTheory.code_rel_def]>>
       gs[stack_removeTheory.compile_def]>>
      gs[stack_removeTheory.init_stubs_def,
         lookup_fromAList]>>
      conj_tac >- (
        gs[Abbr ‘code’]>>gs[lookup_fromAList]>>
        ntac 3 strip_tac>>
        gs[stack_allocTheory.compile_def]>>

        qpat_x_assum ‘word_to_stack$compile _ _ = _’ assume_tac>>
        gs[word_to_stackTheory.compile_def]>>
        pairarg_tac>>gs[]>>
        
        drule word_to_stackProofTheory.compile_word_to_stack_convs>>

        strip_tac>>
        first_x_assum (qspec_then ‘mc.target.config’ assume_tac)>>gs[]>>
        gs[EVERY_EL]>>
                
        cheat)>>
      gs[domain_fromAList, Abbr ‘code’]>>
      ‘∀x. (0:num) INSERT 1 INSERT 2 INSERT x = x ∪ {0; 1; 2}’
        by (strip_tac>>gs[INSERT_DEF,UNION_DEF]>>
            gs[EXTENSION]>>metis_tac[])>>
      irule EQ_TRANS>>
      first_x_assum $ qspec_then ‘set
              (MAP FST
                 (MAP (stack_remove_prog_comp jump off sp)
                    (compile c.data_conf (compile p))))’ assume_tac>>
      pop_assum $ irule_at Any>>
      irule $ METIS_PROVE [] “∀A B C. A = B ⇒ A ∪ C = B ∪ C”>>
      AP_TERM_TAC>>
      gs[MAP_MAP_o]>>gs[MAP_EQ_f])>>
gs[]>>strip_tac>>
gs[]>>
  gs[stack_removeProofTheory.make_init_opt_def]>>
  gs[stack_removeProofTheory.init_reduce_def]>>
  gs[stack_removeProofTheory.init_prop_def]>>

gs[Abbr ‘s'’]>>
gs[wordSemTheory.theWord_def]

simp[INSERT_SING_UNION]>>
        ntac 3 (rewrite_tac[Once INSERT_SING_UNION])>>
                                    
        Cases_on ‘compile c.data_conf (compile p)’>>
        gs[stack_removeTheory.prog_comp_def]>>
        
stack_removeProofTheory.FST_prog_comp

(*************)
                        
  (* apply *)
  gvs[]
QED
(*Abbrev
          (sp =
           mc.target.config.reg_count −
           (LENGTH mc.target.config.avoid_regs + 3))
           *)
