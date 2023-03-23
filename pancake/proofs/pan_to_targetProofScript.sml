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

Theorem word_to_stack_compile_FST:
  word_to_stack_compile mc.target.config wprog = (bitmaps,c'',fs,p) ⇒
  MAP FST p =
  raise_stub_location::store_consts_stub_location::MAP FST wprog
Proof
  strip_tac>>gs[word_to_stackTheory.compile_def]>>
  pairarg_tac>>gs[]>>rveq>>gs[]>>
  drule_then irule word_to_stackProofTheory.MAP_FST_compile_word_to_stack
QED

Theorem pan_to_stack_first_ALL_DISTINCT:
  pan_to_word_compile_prog pan_code = wprog0 ∧
  word_to_word_compile c.word_to_word_conf mc.target.config wprog0 = (col,wprog) ∧
  word_to_stack_compile mc.target.config wprog = (bitmaps,c'',fs,p) ∧
  ALL_DISTINCT (MAP FST pan_code) ⇒
  ALL_DISTINCT (MAP FST p)
Proof
  strip_tac>>drule pan_to_wordProofTheory.first_compile_prog_all_distinct>>
  strip_tac>>
  drule backendProofTheory.compile_to_word_conventions2>>strip_tac>>
  gs[]>>
  qpat_x_assum ‘MAP FST wprog = _’ $ assume_tac o GSYM>>gs[]>>
  drule word_to_stack_compile_FST>>
  strip_tac>>gs[]>>
  drule pan_to_wordProofTheory.pan_to_word_compile_prog_lab_min>>
  strip_tac>>
  gs[GSYM EVERY_MAP]>>EVAL_TAC>>gs[EVERY_MEM]>>
  rw[]>- (first_x_assum $ qspec_then ‘5’ assume_tac>>gs[])>>
  first_x_assum $ qspec_then ‘6’ assume_tac>>gs[]
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
  drule pan_to_wordProofTheory.pan_to_word_compile_lab_pres>>strip_tac>>
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
  drule pan_to_wordProofTheory.pan_to_word_compile_prog_lab_min>>
  gs[GSYM EVERY_MAP, EVERY_MEM]>>ntac 3 strip_tac>>
  first_x_assum $ qspec_then ‘n’ assume_tac>>gs[]
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

(** stack_to_lab$good_code **)

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

Theorem good_dimindex_0w_8w:
   good_dimindex (:α) ⇒ (0w:α word) ≤ 8w ∧ -8w ≤ (0w:α word)
Proof
  strip_tac>>
  fs[WORD_LE,labPropsTheory.good_dimindex_def,word_2comp_n2w,
     dimword_def,word_msb_n2w]
QED

Theorem FLOOKUP_MAP_KEYS_LINV:
  f PERMUTES 𝕌(:α) ⇒
  FLOOKUP (MAP_KEYS (LINV f 𝕌(:α)) m) (i:α) = FLOOKUP m (f i)
Proof
  strip_tac>>
  drule BIJ_LINV_INV>>strip_tac>>
  drule BIJ_LINV_BIJ>>strip_tac>>
  gs[BIJ_DEF]>>
  mp_tac (GEN_ALL $ INST_TYPE [beta|->alpha,gamma|->beta] FLOOKUP_MAP_KEYS_MAPPED)>>
  disch_then $ qspecl_then [‘m’, ‘f i’, ‘LINV f 𝕌(:α)’] mp_tac>>
  gs[]>>
  last_x_assum assume_tac>>
  drule LINV_DEF>>
  disch_then $ qspec_then ‘i’ mp_tac>>
  impl_tac >- gs[]>>
  strip_tac>>pop_assum (fn h => rewrite_tac[h])
QED

(* move to stack_to_labProof *)
Theorem full_make_init_be:
   (FST(full_make_init a b c d e f g h i j k)).be ⇔ h.be
Proof
  fs[stack_to_labProofTheory.full_make_init_def]>>
  fs[stack_allocProofTheory.make_init_def]>>
  simp[stack_removeProofTheory.make_init_any_def,
       stack_removeProofTheory.make_init_opt_def]>>
  every_case_tac>>fs[]>>
  imp_res_tac stackPropsTheory.evaluate_consts>>
  EVAL_TAC>>fs[]>>
  EVAL_TAC>>fs[]
QED

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
  mc.target.get_reg ms mc.len2_reg = s.base_addr ∧
(*  s.memaddrs = addresses (mc.target.get_reg ms mc.len_reg)
             (w2n ((mc.target.get_reg ms mc.ptr_reg) + -1w * (mc.target.get_reg ms mc.len_reg)) DIV (dimindex (:α) DIV 8) − 48)∧*)
(*  (∀a. ∃w.
         mc.target.get_byte ms a =
         get_byte a w mc.target.config.big_endian ∧
         (mk_mem (make_funcs (compile_prog pan_code)) s.memory) (byte_align a) = Word w) ∧*)
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

  qabbrev_tac ‘lorac = λn:num. (ltconf, []:(num # 'a stack_rawcallProof$prog) list, []:'a word list)’>>
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
    gs[Abbr ‘sorac’]>>gs[Abbr ‘lorac’]>>
    simp [lab_to_targetProofTheory.compiler_oracle_ok_def]>>
    ‘ltconf.pos = LENGTH bytes ∧
     ltconf.asm_conf = mc.target.config’
      by (gs[lab_to_targetTheory.compile_def]>>
          drule backendProofTheory.compile_lab_lab_conf>>
          strip_tac>>gs[]>>
          drule backendProofTheory.compile_lab_LENGTH>>
          strip_tac>>gs[]>>
          rveq>>gs[])>>gs[]>>
    gs[stack_to_labTheory.compile_no_stubs_def]>>
    gs[stack_namesTheory.compile_def]>>
    gs[lab_to_targetProofTheory.good_code_def]>>
    gs[labPropsTheory.get_labels_def,backendPropsTheory.restrict_nonzero_def])>>
    gs[]>>

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
      rw[]>>
      gs[stack_to_labProofTheory.good_code_def])>>
     gs[]>>

  ‘memory_assumption c.stack_conf.reg_names bitmaps data_sp labst’
    by (
    gs[stack_to_labProofTheory.memory_assumption_def]>>
    qpat_assum ‘Abbrev (labst = _)’ mp_tac>>
    rewrite_tac[markerTheory.Abbrev_def]>>
    rewrite_tac[lab_to_targetProofTheory.make_init_def,
       labSemTheory.state_component_equality]>>
    simp[]>>strip_tac>>gs[]>>
    gs[backendProofTheory.heap_regs_def]>>

    qpat_x_assum ‘_ (fun2set _)’ assume_tac>>

    rewrite_tac[Once INTER_COMM]>>
    rewrite_tac[UNION_OVER_INTER]>>
    rewrite_tac[Once UNION_COMM]>>
    irule miscTheory.fun2set_disjoint_union>>
    gs[]>>
      conj_tac >- (
      irule backendProofTheory.word_list_exists_imp>>
      gs[]>>
      ‘(w2n:'a word -> num) bytes_in_word = dimindex (:α) DIV 8’ by
        rfs [labPropsTheory.good_dimindex_def,bytes_in_word_def,dimword_def]>>
      conj_tac >- (
        fs [] \\ match_mp_tac IMP_MULT_DIV_LESS \\ fs [w2n_lt]
        \\ rfs [labPropsTheory.good_dimindex_def])>>
              fs [stack_removeProofTheory.addresses_thm]>>
        ‘0 < dimindex (:α) DIV 8’ by
          rfs [labPropsTheory.good_dimindex_def]>>
      gs[]
        \\ qabbrev_tac `a = t.regs q`
        \\ qabbrev_tac `b = t.regs r`
        \\ qpat_x_assum `a <=+ b` assume_tac
        \\ old_drule WORD_LS_IMP \\ strip_tac \\ fs [EXTENSION]
        \\ fs [IN_DEF,PULL_EXISTS,bytes_in_word_def,word_mul_n2w]
        \\ rw [] \\ reverse eq_tac THEN1
         (rw [] \\ fs [] \\ qexists_tac `i * (dimindex (:α) DIV 8)` \\ fs []
          \\ `0 < dimindex (:α) DIV 8` by rfs [labPropsTheory.good_dimindex_def]
          \\ old_drule X_LT_DIV \\ disch_then (fn th => fs [th])
          \\ fs [RIGHT_ADD_DISTRIB]
          \\ fs [GSYM word_mul_n2w,GSYM bytes_in_word_def]
          \\ fs [byte_aligned_mult])
        \\ rw [] \\ fs []
        \\ `i < dimword (:'a)` by metis_tac [LESS_TRANS,w2n_lt] \\ fs []
        \\ qexists_tac `i DIV (dimindex (:α) DIV 8)`
        \\ rfs [alignmentTheory.byte_aligned_def,
             ONCE_REWRITE_RULE [WORD_ADD_COMM] alignmentTheory.aligned_add_sub]
        \\ fs [aligned_w2n]
        \\ old_drule DIVISION
        \\ disch_then (qspec_then `i` (strip_assume_tac o GSYM))
        \\ `2 ** LOG2 (dimindex (:α) DIV 8) = dimindex (:α) DIV 8` by
             (fs [labPropsTheory.good_dimindex_def] \\ NO_TAC)
        \\ fs [] \\ rfs [] \\ `-1w * a + b = b - a` by fs []
        \\ full_simp_tac std_ss []
        \\ Cases_on `a` \\ Cases_on `b`
        \\ full_simp_tac std_ss [WORD_LS,addressTheory.word_arith_lemma2]
        \\ fs [] \\ match_mp_tac DIV_LESS_DIV \\ fs []
        \\ rfs [] \\ fs [] \\ match_mp_tac MOD_SUB_LEMMA \\ fs [])>>
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
  disch_then (qspec_then ‘λn. ((LENGTH bitmaps, c'.lab_conf), [])’ mp_tac)>>   (* later *)

  qmatch_goalsub_abbrev_tac ‘init_state_ok _ _ worac’>>
  ‘¬ NULL bitmaps ∧ HD bitmaps = 4w’
    by (drule word_to_stackProofTheory.compile_word_to_stack_bitmaps>>
        strip_tac>>Cases_on ‘bitmaps’>>gs[])>>
  ‘ALOOKUP wprog raise_stub_location = NONE ∧
   ALOOKUP wprog store_consts_stub_location = NONE’
    by (
    qmatch_asmsub_abbrev_tac ‘word_to_word_compile _ _ wprog0 = _’>>
    qpat_x_assum ‘Abbrev (wprog0 = _)’ (assume_tac o GSYM o REWRITE_RULE [markerTheory.Abbrev_def])>>
    drule pan_to_word_compile_prog_lab_min>>
    gs[GSYM EVERY_MAP]>>
    rewrite_tac[ALOOKUP_NONE, EVERY_MEM]>>
    qpat_x_assum ‘MAP FST _ = MAP FST _’ $ assume_tac o GSYM>>
    strip_tac>>gs[]>>
    gs[wordLangTheory.raise_stub_location_def, EL_MAP,
       wordLangTheory.store_consts_stub_location_def,
       backend_commonTheory.word_num_stubs_def,
       backend_commonTheory.stack_num_stubs_def]>>
    first_assum $ qspec_then ‘5’ assume_tac>>
    first_x_assum $ qspec_then ‘6’ assume_tac>>gs[])>>gs[]>>
  ‘init_state_ok
           (mc.target.config.reg_count −
            (LENGTH mc.target.config.avoid_regs + 5)) sst worac’
    by (
      irule stack_to_labProofTheory.IMP_init_state_ok>>
      gs[]>>
      Cases_on ‘opt’>>gs[]>>rename1 ‘(sst, SOME xxx)’>>
      MAP_EVERY qexists_tac [‘data_sp’, ‘c.data_conf’, ‘labst’, ‘max_heap’, ‘p’, ‘set mc.callee_saved_regs’, ‘c.stack_conf’, ‘sp’, ‘mc.target.config.addr_offset’, ‘TL bitmaps’, ‘xxx’]>>

      ‘4w::TL bitmaps = bitmaps’ by (rveq>>gs[]>>metis_tac[CONS])>>gs[]>>
      conj_tac >-
       (strip_tac>>gs[Abbr ‘worac’]>>strip_tac>>
        pop_assum kall_tac>>
        pop_assum (fn h => once_rewrite_tac[GSYM h])>>gs[])>>
      gs[Abbr ‘worac’]>>
      qpat_x_assum ‘_ = (sst, SOME _)’ mp_tac>>
      gs[Abbr ‘lorac’]>>
      pairarg_tac>>gs[]>>
      gs[word_to_stackTheory.compile_word_to_stack_def]>>
      rveq>>gs[])>>gs[]>>

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
  ‘(sst.be ⇔ s.be) ∧ sst.ffi = ffi’
    by (qmatch_asmsub_abbrev_tac ‘fmi = (sst, opt)’>>
        ‘sst = FST fmi’ by gs[]>>gs[]>>
        reverse conj_tac>-
         (‘labst.ffi = ffi’  
            by (gs[Abbr ‘labst’, lab_to_targetProofTheory.make_init_simp])>>
          irule EQ_TRANS>>pop_assum $ irule_at Any>>
          fs[Abbr ‘fmi’]>>gs[stack_to_labProofTheory.full_make_init_ffi])>>
        irule EQ_TRANS>>fs[Abbr ‘fmi’]>>
        gs[full_make_init_be]>>
        qpat_x_assum ‘Abbrev (labst = _)’ ((fn h => rewrite_tac[h]) o REWRITE_RULE [markerTheory.Abbrev_def])>>
        rewrite_tac[lab_to_targetProofTheory.make_init_def]>>
        simp[labSemTheory.state_component_equality])>>gs[]>>
  ‘ALOOKUP pan_code start = SOME ([],prog)’
    by (drule_all ALOOKUP_ALL_DISTINCT_EL>>strip_tac>>gs[])>>gs[]>>

(*  what's left to show:
    sst.memory = mk_mem (make_funcs (compile_prog pan_code)) s.memory ∧
    sst.mdomain = s.memaddrs ∧
    FLOOKUP sst.store CurrHeap = SOME (Word s.base_addr) *)

  (* maybe use init_store_ok? *)

  fs[stack_to_labProofTheory.full_make_init_def]>>
  Cases_on ‘opt’>>gs[Abbr ‘lorac’]>>
  fs[combinTheory.o_DEF]>>
  fs[stack_removeProofTheory.make_init_opt_def]>>

  qmatch_asmsub_abbrev_tac ‘evaluate (_, sss)’>>
  Cases_on ‘evaluate (init_code (is_gen_gc c.data_conf.gc_kind) max_heap sp, sss)’>>
  rename1 ‘_= (q', r')’>>Cases_on ‘q'’>>gs[]>>

  (* init_code shows here *)

  gs[stack_namesProofTheory.make_init_def]>>
  gs[stack_to_labProofTheory.make_init_def]>>
  gs[stack_allocProofTheory.make_init_def]>>
  gs[stack_removeProofTheory.make_init_any_def]>>

  qpat_x_assum ‘_ = labst.len2_reg’ $ assume_tac o GSYM>>
  qpat_x_assum ‘_ = labst.ptr2_reg’ $ assume_tac o GSYM>>
  qpat_x_assum ‘_ = labst.len_reg’ $ assume_tac o GSYM>>
  qpat_x_assum ‘_ = labst.ptr_reg’ $ assume_tac o GSYM>>
  gs[]>>

  ‘mc.len2_reg ≠ mc.len_reg ∧ mc.ptr2_reg ≠ mc.len_reg ∧
   mc.len2_reg ≠ mc.ptr2_reg’
    by (
    gs[BIJ_DEF, INJ_DEF]>>
    conj_tac >- (
      CCONTR_TAC>>
      last_x_assum $ qspecl_then [‘4’, ‘2’] assume_tac>>
      gs[])>>
    conj_tac >- (
      CCONTR_TAC>>
      last_x_assum $ qspecl_then [‘3’, ‘2’] assume_tac>>
      gs[])>>
    CCONTR_TAC>>
    last_x_assum $ qspecl_then [‘3’, ‘4’] assume_tac>>
    gs[])>>

  ‘init_code_pre sp bitmaps data_sp sss’
    by (
    simp[stack_removeProofTheory.init_code_pre_def]>>
    gs[stack_to_labProofTheory.memory_assumption_def]>>
    gs[Abbr ‘sss’]>>
    gs[FLOOKUP_MAP_KEYS_LINV]>>
    MAP_EVERY qexists_tac [‘ptr2’, ‘ptr3’, ‘ptr4’, ‘bitmap_ptr'’]>>
    gs[]>>
    gs[flookup_fupdate_list]>>
    gs[REVERSE_DEF, ALOOKUP_APPEND]>>
    gs[]>>
    conj_tac >- simp[domain_fromAList, stack_removeTheory.compile_def,
                     stack_removeTheory.init_stubs_def]>>
    conj_tac >- 
     (qpat_x_assum ‘MEM (_ _ sp) _’ $ irule_at Any>>
      simp[Once EQ_SYM_EQ]>>irule LINV_DEF>>
      gs[BIJ_DEF]>>metis_tac[])>>
    conj_tac >- 
     (qpat_x_assum ‘MEM (_ _ (_+1)) _’ $ irule_at Any>>
      simp[Once EQ_SYM_EQ]>>irule LINV_DEF>>
      gs[BIJ_DEF]>>metis_tac[])>>
    (qpat_x_assum ‘MEM (_ _ (_+2)) _’ $ irule_at Any>>
     simp[Once EQ_SYM_EQ]>>irule LINV_DEF>>
     gs[BIJ_DEF]>>metis_tac[]))>>
  ‘code_rel c.stack_conf.jump mc.target.config.addr_offset sp (fromAList (stack_alloc$compile c.data_conf (compile p))) sss.code’
    by (
    simp[stack_removeProofTheory.code_rel_def]>>
    gs[Abbr ‘sss’]>>
    reverse conj_tac >- (
      gs[domain_fromAList]>>
      simp[stack_removeTheory.compile_def]>>
      simp[stack_removeProofTheory.prog_comp_eta]>>
      simp[stack_removeTheory.init_stubs_def]>>
      rewrite_tac[Once UNION_COMM]>>
      simp[MAP_MAP_o, combinTheory.o_DEF]>>simp[LAMBDA_PROD]>>
      ‘set (MAP (λ(p1,p2). p1) (compile c.data_conf (compile p))) =
       set (MAP FST (compile c.data_conf (compile p)))’
        by (
        gs[LIST_TO_SET_MAP]>>
        irule IMAGE_CONG>>rw[]>>pairarg_tac>>gs[])>>
      gs[])>>
    ntac 3 strip_tac>>
    simp[stack_removeTheory.compile_def]>>
    simp[stack_removeProofTheory.prog_comp_eta]>>
    gs[lookup_fromAList]>>
    simp[ALOOKUP_APPEND]>>
    conj_tac >- (
      qpat_x_assum ‘good_code _ p’ mp_tac>>
      simp[stack_to_labProofTheory.good_code_def]>>
      strip_tac>>
      gs[Once (GSYM stack_rawcallProofTheory.stack_rawcall_reg_bound)]>>
      drule_all stack_allocProofTheory.stack_alloc_reg_bound>>
      strip_tac>>
      first_x_assum $ qspec_then ‘c.data_conf’ assume_tac>>
      pop_assum $ mp_tac>>
      gs[EVERY_MEM]>>drule ALOOKUP_MEM>>strip_tac>>strip_tac>>
      first_x_assum $ qspec_then ‘prog'’ assume_tac>>gs[MEM_MAP]>>
      pop_assum $ irule>>qexists_tac ‘(n, prog')’>>gs[])>>
    simp[ALOOKUP_MAP]>>
    drule ALOOKUP_MEM>>
    strip_tac>>
    gs[stack_allocTheory.compile_def]
    >- (
      gs[stack_allocTheory.stubs_def]>>
      gs[stackLangTheory.gc_stub_location_def]>>
      gs[backend_commonTheory.stack_num_stubs_def]>>
      CASE_TAC>>gs[]>>
      gs[stack_removeTheory.init_stubs_def])>>
    gs[MEM_MAP]>>
    Cases_on ‘y’>> gs[stack_allocTheory.prog_comp_def]>>
    gs[stack_rawcallTheory.compile_def]>>
    gs[MEM_MAP]>>
    Cases_on ‘y’>>gs[]>>
    drule word_to_stack_compile_FST>>
    strip_tac>>

    ‘EVERY (λprog. 60 ≤ FST prog) wprog’
      by (
      qpat_x_assum ‘Abbrev (wprog0 = _)’ (assume_tac o GSYM o REWRITE_RULE [markerTheory.Abbrev_def])>>
      drule pan_to_wordProofTheory.pan_to_word_compile_prog_lab_min>>
      gs[GSYM EVERY_MAP])>>
    gs[wordLangTheory.raise_stub_location_def,
       wordLangTheory.store_consts_stub_location_def]>>
    gs[backend_commonTheory.word_num_stubs_def]>>
    gs[backend_commonTheory.stack_num_stubs_def]>>
    gs[GSYM EVERY_MAP]>>

    CASE_TAC>>gs[]>>


    pop_assum mp_tac>>
    simp[stack_removeTheory.init_stubs_def]>>
    ‘MEM q'' (MAP FST p)’ by (gs[MEM_MAP]>>qexists_tac ‘(q'', r''')’>>gs[])>>
    gs[EVERY_MEM]>>
    IF_CASES_TAC>- (first_x_assum $ qspec_then ‘0’ assume_tac>>gs[])>>
    IF_CASES_TAC>- (first_x_assum $ qspec_then ‘1’ assume_tac>>gs[])>>
    IF_CASES_TAC>- (first_x_assum $ qspec_then ‘2’ assume_tac>>gs[])>>
    simp[])>>
  ‘sss.compile_oracle =
   (I ## MAP (stack_remove_prog_comp c.stack_conf.jump mc.target.config.addr_offset sp) ## I) ∘ (λx. (ltconf,[],[])) ∧
   (∀n i p.
      MEM (i,p) (FST (SND ((λx. (ltconf,[]:(num # α stack_rawcallProof$prog) list,[]:α word list)) n))) ⇒
      reg_bound p sp ∧ stack_num_stubs ≤ i + 1) ∧
   lookup stack_err_lab sss.code = SOME (halt_inst 2w) ∧
   max_stack_alloc ≤ max_heap’
    by (
    gs[Abbr ‘sss’]>>
    conj_tac >- gs[FUN_EQ_THM]>>
    gs[lookup_fromAList]>>
    simp[stack_removeTheory.compile_def,stack_removeTheory.init_stubs_def,
         stack_removeTheory.stack_err_lab_def])>>

  drule_then drule stack_removeProofTheory.init_code_thm>>
  rpt (disch_then $ drule_at Any)>>
  disch_then $ qspecl_then [‘is_gen_gc c.data_conf.gc_kind’] assume_tac>>
  gs[]>>

  qabbrev_tac ‘mko = make_init_opt (is_gen_gc c.data_conf.gc_kind) max_heap bitmaps data_sp (λn. (ltconf,[],[])) c.stack_conf.jump mc.target.config.addr_offset sp (fromAList (compile c.data_conf (compile p))) sss’>>
  gs[]>>
  fs[stack_removeProofTheory.make_init_opt_def]>>gs[]>>
  gs[Abbr ‘mko’]>>
  (***)




  (***)
  gs[Abbr ‘sss’]>>

  gs[stack_removeProofTheory.init_prop_def]>>
  gs[stack_removeProofTheory.init_reduce_def]>>
  rveq>>gs[]>>

  (*
gs[targetSemTheory.good_init_state_def]>>
gs[asmPropsTheory.target_state_rel_def]>>
gs[targetSemTheory.target_configured_def]>>
  *)

  ‘store_init (is_gen_gc c.data_conf.gc_kind) sp CurrHeap =
   (INR (sp + 2) :'a word + num)’
    by gs[stack_removeTheory.store_init_def, APPLY_UPDATE_LIST_ALOOKUP]>>
  gs[]>>

  gs[flookup_fupdate_list]>>
  gs[REVERSE_DEF, ALOOKUP_APPEND]>>
  ‘ALL_DISTINCT (MAP FST (MAP
                          (λn.
                             case
                             store_init (is_gen_gc c.data_conf.gc_kind) sp n
                             of
                               INL w => (n,Word w)
                             | INR i => (n,r'.regs ' i)) store_list))’
    by (rewrite_tac[stack_removeTheory.store_list_def,
                    stack_removeTheory.store_init_def,
                    APPLY_UPDATE_LIST_ALOOKUP]>>
        gs[APPLY_UPDATE_LIST_ALOOKUP])>>
  gs[alookup_distinct_reverse]>>
  gs[stack_removeTheory.store_list_def,
     stack_removeTheory.store_init_def,
     APPLY_UPDATE_LIST_ALOOKUP]>>

  qpat_x_assum ‘FLOOKUP r'.regs _ = SOME _’ mp_tac>>
  qpat_x_assum ‘FLOOKUP _ _ = SOME (Word w2)’ mp_tac>>
  qpat_x_assum ‘r'.regs ' _ = Word curr’ mp_tac>>

  simp[FLOOKUP_MAP_KEYS_LINV]>>

  rewrite_tac[flookup_fupdate_list]>>
  rewrite_tac[REVERSE_DEF, ALOOKUP_APPEND]>>
  rewrite_tac[stack_removeTheory.store_list_def]>>
  rewrite_tac[stack_removeTheory.store_init_def]>>
  simp[APPLY_UPDATE_LIST_ALOOKUP]>>

  gs[FLOOKUP_DEF]>>ntac 3 strip_tac>>
  gs[]>>
  ‘labst.regs = (λk. Word (t.regs k))’
    by (
    qpat_x_assum ‘Abbrev (labst = _)’ (mp_tac o REWRITE_RULE [markerTheory.Abbrev_def])>>
    simp[lab_to_targetProofTheory.make_init_def]>>
    simp[labSemTheory.state_component_equality])>>
  ‘labst.regs mc.len_reg = Word (t.regs mc.len_reg)’ by gs[]>>

  (* need target_state_rel *)
  gs[targetSemTheory.good_init_state_def]>>
  gs[asmPropsTheory.target_state_rel_def]>>

  qpat_x_assum ‘∀i. _ ⇒ mc.target.get_reg ms _ = t.regs _’ assume_tac>>
  first_assum $ qspec_then ‘mc.len2_reg’ assume_tac>>gs[]>>
  pop_assum mp_tac>>impl_tac>- 
   gs[asmTheory.reg_ok_def]>>
  strip_tac>>gs[]>>
        
  gs[wordSemTheory.theWord_def]>>

  (* ok till here *)
  (*  ‘r'.memory = labst.mem ∧ r'.mdomain = labst.mem_domain’ by cheat>>*)

      ‘mc.target.config.reg_count −
       (LENGTH mc.target.config.avoid_regs + 2) = sp + 1 ∧
        mc.target.config.reg_count −
          (LENGTH mc.target.config.avoid_regs + 1) = sp + 2 ∧
        mc.target.config.reg_count −
          (LENGTH mc.target.config.avoid_regs + 5) = sp - 2’
       by gs[Abbr ‘sp’]>>
  gs[]>>

  gs[stack_removeProofTheory.init_code_pre_def]>>
  gs[stack_to_labProofTheory.memory_assumption_def]>>
  gs[targetSemTheory.target_configured_def]>>

  gs[FLOOKUP_MAP_KEYS_LINV]>>
  fs[flookup_fupdate_list]>>
  fs[REVERSE_DEF, ALOOKUP_APPEND]>>
  simp[APPLY_UPDATE_LIST_ALOOKUP]>>

  gs[backendProofTheory.heap_regs_def]>>
  gs[wordSemTheory.theWord_def, stack_removeProofTheory.the_SOME_Word_def]>>

  qpat_x_assum ‘_ + 1 = _’ $ assume_tac o GSYM>>gs[]>>
  qpat_x_assum ‘_ + 2 = _’ $ assume_tac o GSYM>>gs[]>>
  qpat_x_assum ‘sp = _’ $ assume_tac o GSYM>>gs[]>>

  gs[stack_removeProofTheory.state_rel_def]>>
  gs[wordSemTheory.theWord_def]>>
  fs[stack_removeProofTheory.the_SOME_Word_def]>>

(*  gs[FLOOKUP_MAP_KEYS_LINV]>>*)
  fs[flookup_fupdate_list]>>
  Cases_on ‘FLOOKUP r'.regs (sp + 1)’>>gs[]>>
  rename1 ‘FLOOKUP _ (sp + 1) = SOME x3’>>
  Cases_on ‘x3’>>gs[]>>
  gs[flookup_thm]>>
  gs[wordSemTheory.theWord_def]>>


  ‘w4 = ptr4 ∧ w3 = ptr3’ by cheat>>
  gs[]>>


  qpat_x_assum ‘_ (fun2set _)’ $ mp_tac>>
  rewrite_tac[GSYM set_sepTheory.STAR_ASSOC]>>
  strip_tac>>
  drule stack_removeProofTheory.memory_fun2set_SUBSET>>
  strip_tac>>
  drule set_sepTheory.fun2set_STAR_IMP>>
  strip_tac>>


  ‘∃z. DISJOINT ’


        
  fs[stack_removeProofTheory.memory_def]>>




----




  gs[stack_removeProofTheory.memory_def]>>
  gs[LAMBDA_PROD]>>




  fs[REVERSE_DEF, ALOOKUP_APPEND]>>
  simp[APPLY_UPDATE_LIST_ALOOKUP]>>


  imp_res_tac FLOOKUP_MAP_KEYS_LINV>>
  fs[]>>

  fs[flookup_fupdate_list]>>
  fs[REVERSE_DEF, ALOOKUP_APPEND]>>
  simp[APPLY_UPDATE_LIST_ALOOKUP]>>

  gs[FLOOKUP_DEF]>>ntac 3 strip_tac>>



  gs[targetSemTheory.good_init_state_def]>>
  gs[targetSemTheory.target_configured_def]>>
  gs[asmPropsTheory.target_state_rel_def]>>



  gs[stack_removeProofTheory.state_rel_def]>>
  gs[flookup_fupdate_list]>>
  gs[REVERSE_DEF, ALOOKUP_APPEND]>>
  gs[wordSemTheory.theWord_def, stack_removeProofTheory.the_SOME_Word_def]>>
  gs[APPLY_UPDATE_LIST_ALOOKUP]>>
  Cases_on ‘FLOOKUP r'.regs (sp + 1)’>>gs[]>>
  rename1 ‘_ = SOME x’>>Cases_on ‘x’>>gs[]>>



  ‘r'.memory = labst.mem’ by cheat>>

  gs[stack_removeProofTheory.state_rel_def]>>
  gs[flookup_fupdate_list]>>
  gs[REVERSE_DEF, ALOOKUP_APPEND]>>
  gs[wordSemTheory.theWord_def, stack_removeProofTheory.the_SOME_Word_def]>>
  gs[APPLY_UPDATE_LIST_ALOOKUP]>>
  Cases_on ‘FLOOKUP r'.regs (sp + 1)’>>gs[]>>
  Cases_on ‘x’>>gs[]>>

  qpat_x_assum ‘Abbrev (labst = _)’ (mp_tac o REWRITE_RULE [markerTheory.Abbrev_def])>>
  simp[lab_to_targetProofTheory.make_init_def]>>
  simp[labSemTheory.state_component_equality]>>
strip_tac>>
gs[]>>

  gs[targetSemTheory.good_init_state_def]>>
  gs[targetSemTheory.target_configured_def]>>
  gs[asmPropsTheory.target_state_rel_def]>>

  gs[stack_to_labProofTheory.memory_assumption_def]>>
  gs[wordSemTheory.theWord_def, stack_removeProofTheory.the_SOME_Word_def]>>
  gs[stack_removeProofTheory.is_SOME_Word_def]>>

  (* equality of memories as functions?? *)



        ‘labst.mem = ∧ labst.mem_domain = ’

    gs[stack_removeProofTheory.state_rel_def]>>
    gs[word_to_stackProofTheory.init_state_ok_def]>>
    gs[stack_to_labProofTheory.memory_assumption_def]>>



  conj_tac >- (
    gs[stack_removeProofTheory.state_rel_def]>>

  gs[flookup_fupdate_list]>>
    gs[REVERSE_DEF, ALOOKUP_APPEND]>>
    gs[wordSemTheory.theWord_def, stack_removeProofTheory.the_SOME_Word_def]>>
  gs[APPLY_UPDATE_LIST_ALOOKUP]>>
    Cases_on ‘FLOOKUP r'.regs (sp + 1)’>>gs[]>>
Cases_on ‘x’>>gs[]>>


  rewrite_tac[stack_removeTheory.store_list_def]>>
  rewrite_tac[stack_removeTheory.store_init_def]>>



    Cases_on ‘x’>>gs[]>>







val _ = export_theory();
