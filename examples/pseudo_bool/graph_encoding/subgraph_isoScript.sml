(*
  Formalization of the subgraph isomorphism encoder (non-induced)
*)
open preamble graph_basicTheory pbcTheory pbc_normaliseTheory;

val _ = new_theory "subgraph_iso";

Definition has_subgraph_iso_def:
  has_subgraph_iso ((vp,ep):graph) ((vt,et):graph) ⇔
  ∃f.
    INJ f (count vp) (count vt) ∧
    (∀a b. is_edge ep a b ⇒ is_edge et (f a) (f b))
End

(* tuple (p,t) represents variable x_{p,t} *)
Type map_var = ``:num # num``

(* For a in vp, vp is mapped to exactly 1 target in vt *)
Definition has_mapping_def:
  has_mapping (a:num) vt =
  (Equal, (GENLIST (λv. (1, Pos (a,v))) vt), 1):map_var pbc
End

Definition one_one_def:
  one_one u vp =
  (GreaterEqual, GENLIST (λb. (1, Neg (b,u))) vp, &vp-1): map_var pbc
End

Definition edge_map_def:
  edge_map (a:num,b:num) (u:num) et =
  (GreaterEqual,
    (1,Neg (a,u)) :: MAP (λv. (1,Pos (b,v))) (neighbours et u),
    1): map_var pbc
End

Definition all_has_mapping_def:
  all_has_mapping vp vt =
  GENLIST (λa. has_mapping a vt) vp
End

Definition all_one_one_def:
  all_one_one vp vt =
  GENLIST (λu. one_one u vp) vt
End

Definition all_edge_map_def:
  all_edge_map (vp,ep) (vt,et) =
  FLAT
  (FLAT (GENLIST (λu.
    (GENLIST (λa.
      MAP (λb. edge_map (a,b) u et) (neighbours ep a)) vp)) vt))
End

Definition encode_def:
  encode (vp,ep) (vt,et) =
  all_has_mapping vp vt ++ all_one_one vp vt ++ all_edge_map (vp,ep) (vt,et)
End

Theorem iSUM_zero:
  (∀x. MEM x ls ⇒ x ≥ 0) ⇒
  iSUM ls ≥ 0
Proof
  Induct_on`ls`>> rw[iSUM_def]>>
  fs[]>>
  first_x_assum(qspec_then`h` assume_tac)>>
  fs[]>>
  intLib.ARITH_TAC
QED

Theorem b2i_eq_1[simp]:
  b2i b = 1 ⇔ b
Proof
  Cases_on`b`>>fs[]
QED

Theorem b2i_eq_0[simp]:
  b2i b = 0 ⇔ ¬b
Proof
  Cases_on`b`>>fs[]
QED

Theorem b2i_geq_zero[simp]:
  b2i b ≥ 0
Proof
  Cases_on`b`>>simp[]
QED

Theorem b2i_iSUM_eq_0:
  (∀x. MEM x ls ⇒ ∃y. x = b2i y) ⇒
  (iSUM ls = 0 ⇔
  ∀j. j < LENGTH ls ⇒ EL j ls = 0)
Proof
  Induct_on`ls`>>rw[iSUM_def]>>fs[]>>
  first_assum(qspec_then`h` assume_tac)>>fs[]>>
  Cases_on`y`>>fs[]
  >- (
    `iSUM ls ≥ 0` by (
      match_mp_tac iSUM_zero>>
      rw[]>>res_tac>>
      rw[])>>
    rw[EQ_IMP_THM]
    >- (
      last_x_assum kall_tac>>
      intLib.COOPER_TAC)>>
    pop_assum(qspec_then`0` mp_tac)>>simp[])
  >>
  rw[EQ_IMP_THM]
  >-
    (Cases_on`j`>>fs[])>>
  first_x_assum (qspec_then`SUC j` mp_tac)>>fs[]
QED

Theorem iSUM_eq_1:
  (∀x. MEM x ls ⇒ ∃y. x = b2i y) ⇒
  (iSUM ls = 1 ⇔
  ∃i. i < LENGTH ls ∧ EL i ls  = 1 ∧
  ∀j. i ≠ j ∧ j < LENGTH ls ⇒ EL j ls = 0)
Proof
  Induct_on`ls`>>rw[iSUM_def]>>fs[]>>
  first_assum(qspec_then`h` assume_tac)>>fs[]>>
  Cases_on`y`>>fs[]>>
  simp[]
  >-(
    DEP_REWRITE_TAC[b2i_iSUM_eq_0]>>
    CONJ_TAC >- metis_tac[]>>
    rw[EQ_IMP_THM]
    >- (
      qexists_tac`0`>>rw[]>>
      Cases_on`j`>>fs[])>>
    `i = 0` by
      (CCONTR_TAC>>
      first_x_assum drule>>fs[])>>
    first_x_assum(qspec_then`SUC j` assume_tac)>>rfs[]>>
    Cases_on`i`>>fs[])
  >>
  rw[EQ_IMP_THM]
  >- (
    qexists_tac`SUC i`>>rw[]>>
    Cases_on`j`>>fs[])>>
  Cases_on`i`>>fs[]>>
  qexists_tac`n`>>rw[]>>
  first_x_assum(qspec_then`SUC j` assume_tac)>>fs[]
QED

Theorem iSUM_sub_b2i_geq_0:
  (∀x. MEM x ls ⇒ ∃y. x = 1 - b2i y) ⇒
  iSUM ls ≤ &(LENGTH ls)
Proof
  Induct_on`ls`>>fs[iSUM_def]>>rw[]>>
  first_assum(qspec_then`h` assume_tac)>>fs[]>>
  Cases_on`y`>>fs[ADD1]>>
  intLib.ARITH_TAC
QED

Theorem iSUM_sub_b2i_geq_0:
  (∀x. MEM x ls ⇒ ∃y. x = 1 - b2i y) ⇒
  (iSUM ls ≥ &(LENGTH ls) ⇔
   ∀i. i < LENGTH ls ⇒ EL i ls = 1)
Proof
  Induct_on`ls`>>
  fs[iSUM_def]>>rw[]>>
  first_assum(qspec_then`h` assume_tac)>>fs[]>>
  Cases_on`y`>>fs[]
  >- (
    `iSUM ls ≤ &(LENGTH ls)` by
      metis_tac[iSUM_sub_b2i_geq_0]>>
    rw[EQ_IMP_THM]
    >-
      (last_x_assum kall_tac>>intLib.ARITH_TAC)>>
    first_x_assum(qspec_then`0` assume_tac)>>fs[])>>
  simp[ADD1,GSYM integerTheory.INT_ADD,intLib.COOPER_PROVE``!n:int. 1 + n ≥ m + 1 ⇔ n ≥ m``]>>
  rw[EQ_IMP_THM]
  >-
    (Cases_on`i`>>fs[])>>
  first_x_assum(qspec_then`SUC i` assume_tac)>>fs[]
QED

Theorem iSUM_sub_b2i_geq:
  (∀x. MEM x ls ⇒ ∃y. x = 1 - b2i y) ⇒
  (iSUM ls ≥ &(LENGTH ls) − 1 ⇔
   ∀i. i < LENGTH ls ∧ EL i ls = 0 ⇒
   ∀j. i ≠ j ∧ j < LENGTH ls ⇒ EL j ls = 1)
Proof
  Induct_on`ls`>>fs[iSUM_def]>>rw[]>>
  simp[ADD1]>>
  first_assum(qspec_then`h` assume_tac)>>fs[]>>
  Cases_on`y`>>fs[]>>
  simp[GSYM integerTheory.INT_ADD,intLib.COOPER_PROVE``!n:int. n +1 -1 = n``]
  >- (
    DEP_REWRITE_TAC[iSUM_sub_b2i_geq_0] >>
    CONJ_TAC >- metis_tac[]>>
    rw[EQ_IMP_THM]
    >- (
      Cases_on`j`>>fs[]>>
      Cases_on`i`>>fs[ADD1]>>
      first_x_assum drule>>fs[])>>
    first_x_assum(qspec_then`0` assume_tac)>>gs[]>>
    first_x_assum(qspec_then`SUC i` assume_tac)>>gs[])>>
  simp[intLib.COOPER_PROVE``!n:int. 1 + n ≥ m ⇔ n ≥ m - 1``]>>
  rw[EQ_IMP_THM]
  >- (
    Cases_on`i`>>fs[ADD1]>>
    first_x_assum drule>>simp[]>>
    Cases_on`j`>>fs[])>>
  first_x_assum(qspec_then`SUC i` assume_tac)>>gs[]>>
  first_x_assum(qspec_then`SUC j` assume_tac)>>gs[]
QED

Theorem iSUM_geq:
  ∀ls.
  (∀x. MEM x ls ⇒ x ≥ 0) ∧
  (∃x. MEM x ls ∧ x ≥ n)
  ⇒
  iSUM ls ≥ n
Proof
  Induct>>rw[iSUM_def]
  >- (
    `iSUM ls ≥ 0` by
      (irule iSUM_zero>>
      metis_tac[])>>
    intLib.ARITH_TAC)>>
  gs[]>>
  last_x_assum mp_tac>>
  impl_tac >- metis_tac[]>>
  first_x_assum(qspec_then`h` assume_tac)>>
  fs[]>>
  intLib.ARITH_TAC
QED

Theorem iSUM_geq_1:
  iSUM ls ≥ 1 /\
  (∀x. MEM x ls ⇒ ∃y. x = b2i y) ⇒
    ∃i. i < LENGTH ls ∧ EL i ls  = 1
Proof
  Induct_on`ls`>>rw[iSUM_def]>>fs[]>>
  first_assum(qspec_then`h` assume_tac)>>fs[]>>
  Cases_on`y`>>fs[]>>
  simp[]
  >- (qexists_tac`0`>>rw[])>>
  qexists_tac`SUC i`>>rw[]
QED

Theorem encode_correct:
  good_graph (vp,ep) ∧
  good_graph (vt,et) ∧
  encode (vp,ep) (vt,et) = constraints ⇒
  (has_subgraph_iso (vp,ep) (vt,et) ⇔ satisfiable (set constraints))
Proof
  rw[EQ_IMP_THM]
  >- (
    fs[has_subgraph_iso_def]>>
    simp[satisfiable_def]>>
    qexists_tac` λ(a,u). f a = u` >>
    rw[encode_def]
    >- (
      rename1`all_has_mapping`>>
      simp[all_has_mapping_def,satisfies_def,MEM_GENLIST,has_mapping_def]>>
      rw[]>>
      simp[satisfies_pbc_def,MAP_GENLIST,o_DEF,eval_lin_term_def]>>
      DEP_REWRITE_TAC[iSUM_eq_1,eval_lin_term_def]>>
      CONJ_TAC>-
        (simp[MEM_GENLIST]>>metis_tac[])>>
      qexists_tac`f a`>>
      CONJ_ASM1_TAC>>fs[EL_GENLIST,INJ_DEF])
    >- (
      rename1`all_one_one`>>
      simp[all_one_one_def,satisfies_def,MEM_GENLIST,one_one_def]>>
      rw[]>>
      simp[satisfies_pbc_def,MAP_GENLIST,o_DEF,eval_lin_term_def]>>
      fs[INJ_DEF]>>
      qmatch_goalsub_abbrev_tac`iSUM ls`>>
      `vp = LENGTH ls` by
        simp[Abbr`ls`]>>
      simp[]>>
      DEP_REWRITE_TAC[iSUM_sub_b2i_geq]>>
      simp[Abbr`ls`]>>
      CONJ_TAC>- (
        simp[MEM_GENLIST]>>
        metis_tac[])>>
      rw[]>>
      gs[EL_GENLIST]>>
      `(f j ≠ u)` by
        metis_tac[]>>
      simp[])
    >- (
      rename1`all_edge_map`>>
      simp[all_edge_map_def,satisfies_def,MEM_GENLIST,MEM_FLAT,edge_map_def]>>
      rw[]>>
      gvs[MEM_FLAT,MEM_GENLIST,MEM_MAP]>>
      fs[MEM_neighbours]>>
      simp[satisfies_pbc_def,MAP_MAP_o,o_DEF,eval_lin_term_def]>>
      `b < vp` by
        (fs[good_graph_eq,is_edge_thm]>>
        metis_tac[MEM_neighbours])>>
      reverse (Cases_on`f a = u`>>rw[]>>simp[iSUM_def])
      >- (
        simp[intLib.COOPER_PROVE``!n:int. 1 + n ≥ 1 ⇔ n ≥ 0``]>>
        match_mp_tac iSUM_zero>>
        simp[MEM_MAP,MEM_neighbours]>>
        rw[]>>
        simp[])>>
      simp[intLib.COOPER_PROVE``!n:int. 1 + n ≥ 1 ⇔ n ≥ 0``]>>
      match_mp_tac iSUM_geq>>rw[]
      >-
        (fs[MEM_MAP]>>pairarg_tac>>simp[])>>
      simp[MEM_MAP,MEM_FILTER,LAMBDA_PROD,PULL_EXISTS,EXISTS_PROD]>>
      qexists_tac`f b`>>simp[]>>
      simp[MEM_neighbours]))>>
  fs[satisfiable_def,has_subgraph_iso_def]>>
  qexists_tac`λn. @m. m < vt ∧ w (n,m)`>>
  fs[satisfies_def,encode_def,SF DNF_ss]>>
  `∀n. n < vp ⇒
    ∃m. m < vt ∧ w (n,m) ∧
    ∀m'. m' < vt ∧ w (n,m') ⇔ m = m'` by (
    fs[all_has_mapping_def,MEM_GENLIST,has_mapping_def,PULL_EXISTS]>>
    rw[]>>
    first_x_assum drule>>
    simp[satisfies_pbc_def,MAP_GENLIST,o_DEF,eval_lin_term_def]>>
    DEP_REWRITE_TAC[iSUM_eq_1]>>
    CONJ_TAC>- (
      simp[MEM_GENLIST]>>metis_tac[])>>
    rw[]>>gs[EL_GENLIST]>>
    asm_exists_tac>>fs[]>>
    CCONTR_TAC>>gs[]>>
    Cases_on`i=m'`>>gs[]>>
    first_x_assum drule>>
    fs[])>>
  rw[]
  >- (
    rw[INJ_DEF]
    >- (
      first_x_assum drule>>strip_tac>>
      fs[])>>
    fs[all_one_one_def,MEM_GENLIST,PULL_EXISTS,one_one_def]>>
    res_tac>>
    gvs[]>>
    last_x_assum drule>>
    simp[satisfies_pbc_def,MAP_GENLIST,o_DEF,eval_lin_term_def]>>
    qmatch_goalsub_abbrev_tac`iSUM ls`>>
    `vp = LENGTH ls` by
      simp[Abbr`ls`]>>
    simp[]>>
    DEP_REWRITE_TAC[iSUM_sub_b2i_geq]>>
    simp[Abbr`ls`]>>
    CONJ_TAC>- (
      simp[MEM_GENLIST]>>
      metis_tac[])>>
    rw[]>>
    first_x_assum drule>>
    simp[EL_GENLIST]>>
    disch_then(qspec_then`n` mp_tac)>>
    simp[])>>
  fs[good_graph_eq]>>
  `a < vp ∧ b < vp` by
    (fs[is_edge_thm]>>
    metis_tac[])>>
  first_assum(qspec_then`a` mp_tac)>>
  first_x_assum(qspec_then`b` drule)>>
  simp[]>>
  rw[]>>
  gvs[]>>
  fs[all_edge_map_def,satisfies_def,MEM_GENLIST,MEM_FLAT,edge_map_def,PULL_EXISTS,MEM_MAP,FORALL_PROD]>>
  `is_edge ep b a` by
    fs[is_edge_thm]>>
  first_x_assum (drule_at (Pos (el 2)))>>
  disch_then (qspec_then`m` mp_tac)>>
  simp[satisfies_pbc_def,iSUM_def,MAP_MAP_o,o_DEF,LAMBDA_PROD,MEM_neighbours,eval_lin_term_def]>>
  disch_then drule>>
  strip_tac>>
  gs[]>>
  drule iSUM_geq_1>>
  simp[MEM_MAP,PULL_EXISTS,MEM_FILTER,FORALL_PROD]>>
  impl_tac >- metis_tac[]>>
  strip_tac>>
  gs[EL_MAP]>>
  qmatch_asmsub_abbrev_tac`(a,ee)`>>
  `m' = ee` by (
    unabbrev_all_tac>>
    metis_tac[MEM_EL,MEM_neighbours,is_edge_thm])>>
  rw[]>>
  `MEM ee (neighbours et m)` by
    metis_tac[EL_MEM,Abbr`ee`]>>
  fs[MEM_neighbours]>>
  metis_tac[is_edge_thm]
QED

(* Encode the variables as strings
  and normalize to ≥ only *)
Definition enc_string_def:
  (enc_string (xp,xt) =
    concat [strlit"x";toString xp;strlit"_";toString xt])
End

Theorem enc_string_INJ:
  INJ enc_string UNIV UNIV
Proof
  rw [INJ_DEF]
  \\ Cases_on`x` \\ Cases_on`y`
  \\ fs [enc_string_def]
  \\ fs [mlstringTheory.concat_def]
  \\ every_case_tac \\ fs []
  \\ full_simp_tac std_ss [GSYM APPEND_ASSOC,APPEND]
  \\ drule mlintTheory.num_to_str_APPEND_11 \\ simp []
  \\ disch_then drule
  \\ disch_then drule
  \\ rw [] \\ gvs []
  \\ rpt (qpat_x_assum ‘_ = strlit _’ (assume_tac o GSYM))
  \\ fs [mlintTheory.num_to_str_11]
QED

Theorem enc_string_goodString:
  goodString (enc_string (xp,xt))
Proof
  gvs [enc_string_def,mlstringTheory.concat_def,goodString_eq_EVERY_goodChar]
  \\ gvs [goodChar_toString]
  \\ EVAL_TAC
QED

Definition full_encode_def:
  full_encode gp gt =
  MAP (map_pbc enc_string) (FLAT (MAP pbc_ge (encode gp gt)))
End

(* TODO: move *)
Theorem satisfies_set_FLAT:
  pbc$satisfies w (set (FLAT ls)) ⇔
  ∀x. MEM x ls ⇒ pbc$satisfies w (set x)
Proof
  rw[EQ_IMP_THM]>>fs[pbcTheory.satisfies_def,MEM_FLAT]>>
  metis_tac[]
QED

Theorem satisfies_FLAT_MAP_pbc_ge:
  satisfies w (set (FLAT (MAP pbc_ge pbf))) ⇔
  satisfies w (set pbf)
Proof
  simp[satisfies_set_FLAT]>>
  rw[EQ_IMP_THM]
  >- (
    rw[satisfies_def]>>fs[MEM_MAP,PULL_EXISTS]>>
    first_x_assum drule>>
    metis_tac[pbc_ge_thm])>>
  fs[MEM_MAP]>>
  metis_tac[pbc_ge_thm,satisfies_def]
QED

Theorem satisfiable_FLAT_MAP_pbc_ge:
  satisfiable (set (FLAT (MAP pbc_ge pbf))) ⇔
  satisfiable (set pbf)
Proof
  simp[satisfiable_def]>>
  metis_tac[satisfies_FLAT_MAP_pbc_ge]
QED

Theorem full_encode_correct:
  good_graph gp ∧
  good_graph gt ⇒
  (has_subgraph_iso gp gt ⇔ satisfiable (set (full_encode gp gt)))
Proof
  rw[full_encode_def]>>
  simp[LIST_TO_SET_MAP]>>
  DEP_REWRITE_TAC[satisfiable_INJ_iff]>>
  rw[]
  >- (
    assume_tac enc_string_INJ>>
    drule INJ_SUBSET>>
    disch_then match_mp_tac>>
    simp[])>>
  simp[satisfiable_FLAT_MAP_pbc_ge] >>
  metis_tac[encode_correct,PAIR,pbc_ge_thm]
QED

(* The theorem relating to sem_concl *)
Theorem full_encode_sem_concl:
  good_graph gp ∧
  good_graph gt ∧
  sem_concl (set (full_encode gp gt)) NONE concl
  ⇒
  case concl of
    DSat => has_subgraph_iso gp gt
  | DUnsat => ¬ has_subgraph_iso gp gt
  | _ => T
Proof
  rw[]>>
  assume_tac full_encode_correct>>gs[]>>
  every_case_tac>>fs[sem_concl_def,unsatisfiable_def]
QED

Definition GENLIST_AUX_gen_def:
  (GENLIST_AUX_gen f 0 l = l) ∧
  (GENLIST_AUX_gen f (SUC n) l =
    GENLIST_AUX_gen f n (f n l))
End

Theorem GENLIST_AUX_gen_append:
  ∀xs.
  GENLIST_AUX_gen ($++ o f) n xs ++ y =
  GENLIST_AUX_gen ($++ o f) n (xs ++ y)
Proof
  Induct_on`n`>>simp[GENLIST_AUX_gen_def]
QED

Theorem FLAT_GENLIST_GENLIST_AUX_gen:
  ∀y.
  FLAT (GENLIST f n) ++ y =
  GENLIST_AUX_gen ($++ o f) n y
Proof
  Induct_on`n`>>rw[GENLIST_AUX_gen_def,GENLIST]>>
  simp[GENLIST_AUX_gen_append]
QED

Theorem FLAT_GENLIST_GENLIST_AUX_gen_nil:
  FLAT (GENLIST f n) =
  GENLIST_AUX_gen ($++ o f) n []
Proof
  simp[GSYM FLAT_GENLIST_GENLIST_AUX_gen]
QED

Theorem GENLIST_FLAT:
  GENLIST (λx. FLAT (f x)) n =
  MAP FLAT (GENLIST f n)
Proof
  simp[MAP_GENLIST,o_DEF]
QED

Definition FLAT2_def:
  FLAT2 [] = [] ∧
  FLAT2 (ls::lss) =
    FOLDR $++ (FLAT2 lss) ls
End

Theorem FOLDR_APPEND_FOLDR:
  FOLDR $++ y x ++ z =
  FOLDR $++ (y ++ z) x
Proof
  Induct_on`x`>>rw[]
QED

Theorem FLAT_APPEND_FOLDR:
  FLAT x ++ y =
  FOLDR $++ y x
Proof
  rw[FLAT_FOLDR,FOLDR_APPEND_FOLDR]
QED

Theorem FLAT2_FLAT_FLAT:
  ∀ls.
  FLAT (FLAT ls) = FLAT2 ls
Proof
  Induct>>rw[FLAT2_def]>>
  pop_assum sym_sub_tac>>
  simp[FLAT_APPEND_FOLDR]
QED

Theorem GENLIST_AUX_gen_SmartAppend:
  ∀ls ls'.
  append ls' = ls ⇒
  GENLIST_AUX_gen ($++ o f) n ls =
  append (GENLIST_AUX_gen (SmartAppend o List o f) n ls')
Proof
  Induct_on`n`>>rw[GENLIST_AUX_gen_def]
QED

Theorem GENLIST_AUX_gen_SmartAppend_Nil:
  GENLIST_AUX_gen ($++ o f) n [] =
  append (GENLIST_AUX_gen (SmartAppend o List o f) n Nil)
Proof
  match_mp_tac GENLIST_AUX_gen_SmartAppend>>simp[]
QED

Theorem GENLIST_AUX_gen_SmartAppend_append:
  GENLIST_AUX_gen ($++ o f) n (append ls') =
  append (GENLIST_AUX_gen (SmartAppend o List o f) n ls')
Proof
  match_mp_tac GENLIST_AUX_gen_SmartAppend>>simp[]
QED

Theorem GENLIST_AUX_gen_cancel_List_append:
  ∀y.
  append (GENLIST_AUX_gen (SmartAppend o List o append o f) n y) =
  append (GENLIST_AUX_gen (SmartAppend o f) n y)
Proof
  Induct_on`n`>>rw[GENLIST_AUX_gen_def]>>
  cheat
QED

Theorem full_encode_eq:
  full_encode (q,r) (q',r') =
  append
     (GENLIST_AUX_gen
        (λx.
             SmartAppend
               (List
                  [map_pbc enc_string
                     (GreaterEqual,GENLIST (λx'. (1,Pos (x,x'))) q',1);
                   map_pbc enc_string
                     (GreaterEqual,
                      flip_coeffs (GENLIST (λx'. (1,Pos (x,x'))) q'),-1)])) q
        (GENLIST_AUX_gen
           (λx.
                SmartAppend
                  (List
                     [map_pbc enc_string
                        (GreaterEqual,GENLIST (λx'. (1,Neg (x',x))) q,&q − 1)]))
           q'
           (GENLIST_AUX_gen
              (λu.
                   SmartAppend
                     (GENLIST_AUX_gen
                        (λx.
                             SmartAppend
                               (List
                                  (MAP
                                     (λx'.
                                          map_pbc enc_string
                                            (GreaterEqual,
                                             (1,Neg (x,u))::
                                               MAP (λx. (1,Pos (x',x)))
                                                 (neighbours r' u),1))
                                     (neighbours r x)))) q Nil)) q' Nil)))
Proof
  rw[full_encode_def,encode_def]>>
  simp[MAP_FLAT,all_edge_map_def,MAP_GENLIST,o_DEF,MAP_MAP_o,edge_map_def,pbc_ge_def,FLAT_FLAT,FLAT_MAP_SING,all_has_mapping_def,has_mapping_def,all_one_one_def,one_one_def]>>
  simp[FLAT_GENLIST_GENLIST_AUX_gen_nil,GENLIST_AUX_gen_append]>>
  simp[GENLIST_AUX_gen_SmartAppend_Nil,GSYM o_DEF]>>
  simp[GENLIST_AUX_gen_cancel_List_append]>>
  simp[GENLIST_AUX_gen_SmartAppend_append]>>
  simp[o_DEF]
QED

val _ = export_theory();
