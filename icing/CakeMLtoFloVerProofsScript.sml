(* HOL4 *)
open machine_ieeeTheory realTheory realLib RealArith;
(* CakeML *)
open semanticPrimitivesTheory terminationTheory compilerTheory;
(* FloVer *)
open ExpressionsTheory ExpressionSemanticsTheory CommandsTheory
     EnvironmentsTheory IEEE_connectionTheory
     FloverMapTheory TypeValidatorTheory;
(* Icing *)
open CakeMLtoFloVerTheory CakeMLtoFloVerLemsTheory;
open preamble;

val _ = new_theory "CakeMLtoFloVerProofs";

(* TODO: Move to HOL4 distrib *)
Theorem float_is_finite_sandwich:
  ∀ (w1:('a,'b) float) (w2:('a,'b) float) (w3:('a,'b) float).
  float_less_equal w1 w2 ∧
  float_less_equal w2 w3 ∧
  float_is_finite w1 ∧
  float_is_finite w3 ⇒
  float_is_finite w2
Proof
  rpt strip_tac
  \\ fs[binary_ieeeTheory.float_is_finite_def,
        binary_ieeeTheory.float_less_equal_def]
  \\ Cases_on ‘float_value w1’ \\ fs[]
  \\ Cases_on ‘float_value w3’ \\ fs[]
  \\ Cases_on ‘float_compare w1 w2’ \\ fs[]
  \\ Cases_on ‘float_compare w2 w3’ \\ rfs[binary_ieeeTheory.float_compare_def]
  \\ Cases_on ‘float_value w2’ \\ fs[]
  \\ Cases_on ‘w2.Sign = 1w’ \\ fs[]
QED

Theorem fp64_isFinite_sandwich:
  ∀ w1 w2 w3.
    fp64_lessEqual w1 w2 ∧
    fp64_lessEqual w2 w3 ∧
    fp64_isFinite w1 ∧
    fp64_isFinite w3 ⇒
    fp64_isFinite w2
Proof
  fs[fp64_lessEqual_def, fp64_isFinite_def]
  \\ rpt strip_tac
  \\ irule float_is_finite_sandwich
  \\ fsrw_tac [SATISFY_ss] []
QED

Theorem closest_such_0:
  ∀ (f:('a, 'b) float).
  closest_such (λ a. ~word_lsb a.Significand) float_is_finite 0 = f ⇒
  f = float_plus_zero (:'a # 'b) ∨ f = float_minus_zero (:'a # 'b)
Proof
  rpt strip_tac \\ rveq
  \\ fs[binary_ieeeTheory.closest_such_def]
  \\ SELECT_ELIM_TAC \\ rpt strip_tac
  >- (
    fs[binary_ieeeTheory.is_closest_def]
    \\ qexists_tac ‘float_plus_zero (:'a # 'b)’
    \\ fs[binary_ieeeTheory.float_is_finite, IN_DEF,
          binary_ieeeTheory.zero_properties, binary_ieeeTheory.zero_to_real,
          ABS_POS]
    \\ rpt strip_tac
    \\ fs[wordsTheory.word_lsb_def, binary_ieeeTheory.float_plus_zero_def]
    \\ pop_assum (fn thm => assume_tac (EVAL_RULE thm)) \\ fs[])
  \\ fs[binary_ieeeTheory.is_closest_def]
  \\ last_x_assum (qspec_then ‘float_plus_zero (:'a # 'b)’ mp_tac)
  \\ simp[binary_ieeeTheory.float_is_finite, IN_DEF,
          binary_ieeeTheory.zero_properties, binary_ieeeTheory.zero_to_real,
          ABS_POS]
  \\ rpt strip_tac
  \\ ‘float_is_zero x’ by (fs[binary_ieeeTheory.float_is_zero_to_real])
  \\ fs[binary_ieeeTheory.float_is_zero, binary_ieeeTheory.float_plus_zero_def,
        binary_ieeeTheory.float_minus_zero_def]
  \\ Cases_on ‘x’ \\ Cases_on ‘c’ \\ Cases_on ‘n’ \\ fs[]
  \\ TRY (rename1 ‘SUC n < 2’ \\ Cases_on ‘n’)
  \\ fs[binary_ieeeTheory.float_negate_def, binary_ieeeTheory.float_component_equality]
QED

Theorem isFloVerExps_toFloVerExp_succeeds:
  ∀ es.
    isFloVerExps es ⇒
    ∀ e. MEM e es ⇒
      ∀ ids freshId.
        ∃ ids2 freshId2 fexp.
        toFloVerExp ids freshId e = SOME (ids2, freshId2, fexp)
Proof
  ho_match_mp_tac isFloVerExps_ind
  \\ rpt strip_tac \\ rfs [] \\ rveq \\ TRY (fs[isFloVerExps_def]\\ NO_TAC)
  >- (fs[isFloVerExps_def, toFloVerExp_def, lookupCMLVar_def]
      \\ rpt (TOP_CASE_TAC \\ fs[]))
  \\ Cases_on ‘op’ \\ fs[isFloVerExps_def, quantHeuristicsTheory.LIST_LENGTH_3]
  \\ rveq \\ fs[]
  >- (
    Cases_on ‘f’ \\ fs[] \\ rveq \\ fs[]
    \\ simp[toFloVerExp_def]
    \\ first_x_assum (qspecl_then [‘ids’,‘freshId’] assume_tac) \\ fs[])
  >- (
     simp[toFloVerExp_def]
     \\ first_assum (qspec_then ‘e1’ assume_tac)
     \\ first_x_assum (qspec_then ‘e2’ assume_tac)
     \\ fs[]
     \\ last_x_assum (qspecl_then [‘ids’, ‘freshId’] assume_tac) \\ fs[]
     \\ last_x_assum (qspecl_then [‘ids2’, ‘freshId2’] assume_tac) \\ fs[])
  \\ simp[toFloVerExp_def]
  \\ first_assum (qspec_then ‘e1’ assume_tac)
  \\ first_assum (qspec_then ‘e2’ assume_tac)
  \\ first_x_assum (qspec_then ‘e3’ assume_tac)
  \\ fs[]
  \\ last_x_assum (qspecl_then [‘ids’, ‘freshId’] assume_tac) \\ fs[]
  \\ last_x_assum (qspecl_then [‘ids2’, ‘freshId2’] assume_tac) \\ fs[]
  \\ rename1 ‘toFloVerExp ids2 freshId2 e2 = SOME (ids3, freshId3, fexp2)’
  \\ last_x_assum (qspecl_then [‘ids3’, ‘freshId3’] assume_tac) \\ fs[]
QED

(*
Theorem isFloVerCmd_toFloVerCmd_succeeds:
  ∀ e ids freshId.
    isFloVerCmd e ⇒
    ∃ ids2 freshId2 f.
      toFloVerCmd ids freshId e = SOME (ids2, freshId2, f)
Proof
  ho_match_mp_tac isFloVerCmd_ind
  \\ rpt strip_tac \\ fs[isFloVerCmd_def, toFloVerCmd_def]
  >- (
   Cases_on ‘so’ \\ fs[lookupCMLVar_def, updateTheory.FIND_def]
   \\ drule isFloVerExps_toFloVerExp_succeeds \\ fs[]
   \\ disch_then (qspecl_then [‘ids’, ‘freshId’] assume_tac) \\ fs[]
   \\ first_x_assum (qspecl_then [‘appendCMLVar (Short x) freshId2 ids2’, ‘freshId2 + 1’] assume_tac)
   \\ fs[])
  >- (
   drule isFloVerExps_toFloVerExp_succeeds
    \\ disch_then (qspecl_then [‘App op exps’,‘ids’, ‘freshId’] assume_tac) \\ fs[])
  \\ fs[toFloVerExp_def]
  \\ Cases_on ‘lookupCMLVar x ids’ \\ fs[]
  \\ rename1 ‘lookupCMLVar x ids = SOME v’
  \\ Cases_on ‘v’ \\ fs[]
QED
*)

(**
  If toFloVerPre constructs a precondition from a CakeML precondition
  with multiple constraints it cannot overwrite bound variables *)
Theorem toFloVerPre_bind_single:
  ∀ e1 e2 ids floverP dVars floverP2 dVars2 x lo hi n.
    toFloVerPre [Log And e1 e2] (ids:((string, string) id # num) list) =
      SOME (floverP,dVars) ⇒
    getInterval (Log And e1 e2) = NONE (* compound case *) ∧
    getInterval e1 = SOME (x, lo, hi) ∧
    toFloVerPre [e2] ids = SOME (floverP2, dVars2) ∧
    lookupCMLVar (Short x) ids = SOME (Short x,n) ⇒
    ~ (Short x IN freevars [e2])
Proof
  rpt strip_tac \\ fs[toFloVerPre_def]
  \\ Cases_on ‘FIND (λ m. n = m) dVars2’ \\ fs[] \\ rveq
  \\ imp_res_tac toFloVerPre_freevar_FIND \\ fs[] \\ rveq \\ fs[]
QED

(**
  Relation: v_eq
  Arguments:
    The CakeML value v, a real number r, and a FloVer type m.
  The predicate returns true, iff either m is REAL, and v represents exactly the
  real number r, or m is M64 for a 64-bit double number, v is a double value or
  a value tree, and r is the translation to reals of v. **)
Definition v_eq_def:
  v_eq (FP_WordTree fp) r M64 = (r = fp64_to_real (compress_word fp)) ∧
  v_eq (Litv (Word64 w)) r M64 = (r = fp64_to_real w) ∧
  v_eq (Real r1) r2 REAL = (r1 = r2) ∧
  v_eq _ _ _ = F
End

Triviality v_eq_float:
  v_eq (Litv (Word64 w)) r m ⇔ ((m = M64) ∧ r = fp64_to_real w)
Proof
  Cases_on ‘m’ \\ fs[v_eq_def]
QED

Triviality v_eq_valtree:
  v_eq (FP_WordTree fp) r m ⇔ ((m = M64) ∧ r = fp64_to_real (compress_word fp))
Proof
  Cases_on ‘m’ \\ fs[v_eq_def]
QED

Triviality v_eq_real:
  v_eq v r REAL ⇔ v = Real r
Proof
  Cases_on ‘v’ \\ fs[v_eq_def]
QED

(**
  Relation: env_sim
  Arguments:
    The CakeML environment env, the FloVer environment E, and a set of pairs of
    CakeML * FloVer variables, and a type environment Gamma
  The environments env and E are in relation with each other for the set of
  variables fVars under the type assignment Gamma,
  if and only if for every pair of variables (cake_id, flover_id):
  if the CakeML environment binds cake_id, the FloVer environment must bind
  flover_id to a value r that is in relation with the CakeML value for the type
  in Gamma, and
  if the FloVer environment binds flover_id, and has a type in Gamma, the
  the CakeML environment binds the variable cake_id to a value that is in
  relation with the FloVer value under the type from Gamma **)
Definition env_sim_def:
  env_sim env E fVars Gamma =
    (∀ (cake_id:(string, string) id) (flover_id:num).
     (cake_id, flover_id) IN fVars ⇒
      (∀ v.
        nsLookup env cake_id = SOME v ⇒
        ∃ r m. E flover_id = SOME r ∧ Gamma (Var flover_id) = SOME m ∧ v_eq v r m) ∧
      (∀ r m.
       E flover_id = SOME r ∧
       Gamma (Var flover_id) = SOME m ⇒
        ∃ v. nsLookup env cake_id = SOME v ∧ v_eq v r m))
End

Theorem getInterval_preserves_bounds:
  ∀ e lo hi (st:α semanticPrimitives$state) env st2 E ids
    freshId fVars x y z (Gamma:real expr -> mType option).
    getInterval e = SOME (x, lo, hi) ∧
    st.fp_state.canOpt = FPScope NoOpt ∧
    evaluate st env [e] = (st2, Rval [Boolv T]) ∧
    env_sim env.v E fVars Gamma ∧
    ids_unique ids freshId ∧
    (∀ x. x IN freevars [e] ⇒ ∃ y. lookupCMLVar x ids = SOME (x,y) ∧ (x,y) IN fVars) ∧
    lookupFloVerVar y ids = SOME (Short x, y) ∧
    lookupCMLVar (Short x) ids = SOME (Short x, z) ⇒
    ∃ v.
      E y = SOME v ∧
      FST ((λ n. if n = z then (lo,hi) else (0,0)) y) ≤ v ∧
      v ≤ SND ((λ n. if n = z then (lo,hi) else (0,0)) y)
Proof
  rpt strip_tac
  \\ first_assum (mp_then Any assume_tac getInterval_inv)
  \\ fs[] \\ rveq
  \\ ‘y = z’ by (fs[ids_unique_def])
  \\ rveq \\ fs[]
  \\ qpat_x_assum ‘evaluate _ _ _ = _’ mp_tac
  \\ simp[evaluate_def]
  \\ Cases_on ‘nsLookup env.v (Short x)’
  \\ simp[astTheory.getOpClass_def, astTheory.isFpBool_def, do_app_def,
          fp_translate_def]
  \\ rename1 ‘nsLookup env.v (Short x) = SOME v’
  \\ fs[env_sim_def] \\ first_x_assum (qspecl_then [‘Short x’, ‘y’] assume_tac)
  \\ rfs[]
  \\ Cases_on ‘v’ \\ simp[fp_translate_def]
  THENL [rename1 ‘Litv l’ \\ Cases_on ‘l’
         \\ simp [fp_translate_def],
         ALL_TAC]
  \\ simp [do_log_def, fpValTreeTheory.fp_cmp_def, fpSemTheory.fp_cmp_comp_def,
           fpSemTheory.compress_word_def, fpSemTheory.compress_bool_def]
  THENL [
    Cases_on ‘fp64_lessEqual w1 c’,
    Cases_on ‘fp64_lessEqual w1 (compress_word f)’]
  \\ simp[evaluate_def, astTheory.getOpClass_def,
          astTheory.isFpBool_def, do_app_def, fp_translate_def]
  \\ simp[fpValTreeTheory.fp_cmp_def, fpSemTheory.fp_cmp_comp_def,
          fpSemTheory.compress_word_def, fpSemTheory.compress_bool_def]
  \\ rpt strip_tac \\ rveq
  \\ first_x_assum (qspec_then ‘r’ assume_tac)
  \\ fs[v_eq_def, fp64_to_real_def, fp64_isFinite_def, fp64_lessEqual_def]
  THENL [
    ‘float_is_finite (fp64_to_float c)’
      by (irule float_is_finite_sandwich \\ fsrw_tac [SATISFY_ss] []),
    ‘float_is_finite (fp64_to_float c)’
      by (irule float_is_finite_sandwich \\ fsrw_tac [SATISFY_ss] []),
    ‘float_is_finite (fp64_to_float (compress_word f))’
      by (irule float_is_finite_sandwich \\ fsrw_tac [SATISFY_ss] []),
    ‘float_is_finite (fp64_to_float (compress_word f))’
      by (irule float_is_finite_sandwich \\ fsrw_tac [SATISFY_ss] [])]
  \\ res_tac
  \\ fs[v_eq_float, v_eq_valtree] \\ rveq \\ simp[fp64_to_real_def]
  \\ metis_tac [lift_ieeeTheory.float_le]
QED

(**
  Prove a relation between the CakeML precondition and the translated
  FloVer precondition.
  If the CakeML precondition is true (i.e. evaluate terminates with Boolv True)
  and the FloVer and CakeML environments agree on the values for the variables
  of the precondition, then the FloVer environment must respect the precondition
  too **)
Theorem toFloVerPre_preserves_bounds:
  ∀ cake_P ids floverP dVars (Gamma:real expr -> mType option).
    (* We can extract a precondition *)
    toFloVerPre cake_P (ids:((string, string) id # num) list) = SOME (floverP,dVars) ⇒
    ∀ st (st2:α semanticPrimitives$state) env E fVars freshId.
      st.fp_state.canOpt = FPScope NoOpt ∧
      (* the free variables are paired up in the id list, and defined *)
      env_sim env.v E fVars Gamma ∧
      ids_unique ids freshId ∧
      (∀ x. x IN freevars cake_P ⇒ ∃ y. lookupCMLVar x ids = SOME (x,y) ∧ (x,y) IN fVars) ∧
      (* the precondition can be evaluated to True *)
      evaluate st env cake_P = (st2, Rval ([Boolv T])) ⇒
      ∀ n x.
        lookupFloVerVar n ids = SOME (x,n) ∧
        x IN freevars cake_P ⇒
      ∃ v. E n = SOME v ∧
      IVlo (floverP n) ≤ v ∧
      v ≤ IVhi (floverP n)
Proof
  ho_match_mp_tac toFloVerPre_ind
  \\ rpt strip_tac \\ fs[toFloVerPre_def]
  \\ qpat_x_assum ‘_ = SOME (floverP, _)’ mp_tac
  \\ reverse TOP_CASE_TAC \\ fs[]
  (* Base case: top expression is an interval constraint *)
  >- (
    rpt (TOP_CASE_TAC \\ fs[])
    \\ rpt strip_tac \\ rveq
    \\ imp_res_tac getInterval_inv \\ rveq \\ fs[] \\ rveq
    \\ drule getInterval_preserves_bounds
    \\ rpt (disch_then drule)
    \\ disch_then (qspecl_then [‘n’, ‘r’] mp_tac) \\ impl_tac
    \\ fs[])
  \\ rpt (TOP_CASE_TAC \\ fs[])
  \\ rpt strip_tac \\ rveq
  \\ qpat_x_assum ‘evaluate _ _ _ = _’ mp_tac
  \\ simp[evaluate_def]
  \\ ntac 2 (TOP_CASE_TAC \\ fs[])
  \\ simp[do_log_def]
  \\ rename1 ‘evaluate st env [e1] = (st1, Rval v)’
  \\ reverse (Cases_on ‘HD v = Boolv T’) \\ fs[]
  >- (Cases_on ‘HD v = Boolv F’ \\ fs[])
  \\ strip_tac \\ fs[]
  \\ first_x_assum (qspecl_then [‘Gamma’,‘st1’, ‘st2’, ‘env’, ‘E’, ‘fVars’, ‘freshId’] mp_tac)
  \\ impl_tac \\ fs[]
  >- (imp_res_tac fpSemPropsTheory.evaluate_fp_opts_inv \\ fs[freevars_def])
  \\ rpt strip_tac \\ imp_res_tac evaluatePropsTheory.evaluate_sing
  \\ fs[] \\ rveq \\ fs[freevars_def]
  (* Base case again *)
  >- (
    imp_res_tac getInterval_inv \\ rveq \\ fs[] \\ rveq
    \\ drule getInterval_preserves_bounds
    \\ rpt (disch_then drule)
    \\ imp_res_tac lookupCMLVar_id_l \\ rveq
    \\ disch_then (qspecl_then [‘n’, ‘r’] mp_tac) \\ impl_tac
    \\ fs[]
    \\ ‘n = r’ by (fs[ids_unique_def])
    \\ rveq \\ fs[])
  \\ res_tac \\ qexists_tac ‘v’
  \\ fs[] \\ rveq
  \\ ‘n ≠ r’ suffices_by (fs[])
  \\ CCONTR_TAC \\ fs[] \\ rveq
  \\ imp_res_tac lookupCMLVar_id_l \\ rveq
  \\ ‘n = y’ by (fs[ids_unique_def])
  \\ rveq \\ fs[]
  \\ ‘x = Short q’ by (fs[ids_unique_def])
  \\ rveq \\ fs[]
  \\ imp_res_tac getInterval_inv
  \\ rename1 ‘toFloVerPre [e2] ids = SOME (flover_P, ids2)’
  \\ qspecl_then [‘e1’, ‘e2’, ‘ids’] mp_tac toFloVerPre_bind_single
  \\ simp[toFloVerPre_def] \\ rveq \\ fs[]
QED

Theorem approxEnv_construct:
  ∀ E1 Gamma A fVars.
    (∀ x. ~ (x  IN domain fVars) ⇒ E1 x = NONE) ∧
    (∀ x. x IN domain fVars ⇒ Gamma (Var x) = SOME M64) ∧
    (∀ x. x IN domain fVars ⇒ ∃ v. E1 x = SOME v) ∧
    (∀ x v. E1 x = SOME v ⇒ (normalizes (:52 # 11) v ∨ v = 0)) ⇒
    approxEnv E1
              Gamma A fVars LN
              (toREnv
               (λ n. case E1 n of
                |NONE => NONE
                | SOME v => SOME (float_to_fp64 (round roundTiesToEven v))))
Proof
  fs[approxEnv_def] \\ rpt strip_tac
  >- (
    res_tac \\ fs[toREnv_def])
  \\ res_tac \\ fs[toREnv_def]
  \\ simp[fp64_to_float_float_to_fp64]
  \\ ‘normalizes (:52 # 11) v ∨ v = 0’
    by (first_x_assum irule \\ fsrw_tac [SATISFY_ss] [])
  >- (
    imp_res_tac lift_ieeeTheory.relative_error
    \\ simp[MachineTypeTheory.computeError_def, MachineTypeTheory.mTypeToR_def]
    \\ rewrite_tac [REAL_LDISTRIB, REAL_MUL_RID, real_sub, REAL_NEG_ADD,
                    REAL_ADD_ASSOC]
    \\ fs[ABS_NEG, ABS_MUL]
    \\ irule REAL_LE_RMUL_IMP \\ fs[ABS_POS])
  \\ rveq \\ fs[binary_ieeeTheory.round_def, binary_ieeeTheory.threshold]
  \\ Q.ISPEC_THEN ‘f:(52,11) float’
                  (assume_tac o SIMP_RULE std_ss [] o GEN_ALL) closest_such_0
  \\ fs[binary_ieeeTheory.zero_to_real, MachineTypeTheory.computeError_def]
QED

Theorem prepareGamma_is_64Bit:
  ∀ floverVars. is64BitEnv (prepareGamma floverVars)
Proof
  Induct_on ‘floverVars’
  \\ fs[prepareGamma_def, is64BitEnv_def,
        FloverMapTree_empty_def, FloverMapTree_find_def, map_find_add]
  \\ rpt strip_tac \\ every_case_tac \\ rveq
  \\ fs[ExpressionAbbrevsTheory.toRExpMap_def, FloverMapTheory.map_find_add]
  \\ res_tac
QED

Theorem eval_expr_real:
  ∀ Gamma E e v m.
  (∀ x m. Gamma x = SOME m ⇒ m = REAL) ∧
  eval_expr E Gamma (toREval e) v m ⇒
  m = REAL
Proof
  Induct_on ‘e’ \\ rpt strip_tac
  \\ fs[Once toREval_def, Once eval_expr_cases] \\ rveq
  \\ res_tac
QED

Theorem CakeML_FloVer_real_sim_exp:
  ∀ varMap freshId f theIds freshId2 theExp E env fVars st Gamma v.
    toFloVerExp varMap freshId f = SOME (theIds, freshId2, theExp) ∧
    ids_unique varMap freshId ∧
    st.fp_state.real_sem ∧
    env_sim env.v E fVars Gamma ∧
    (∀ x m. Gamma x = SOME m ⇒ m = REAL) ∧
    (∀ x. x IN freevars [f] ⇒ ∃ y. lookupCMLVar x varMap = SOME (x,y) ∧ (x,y) IN fVars) ∧
    eval_expr E Gamma (toREval (toRExp theExp)) v REAL ⇒
    ∃ st2. evaluate st env [toRealExp f] = (st2, Rval [Real v])
Proof
  ho_match_mp_tac toFloVerExp_ind
  \\ rpt strip_tac
  \\ ((rename1 ‘App op exps’ \\ imp_res_tac toFloVerExp_App_cases)
     ORELSE
     (qpat_x_assum ‘toFloVerExp _ _ _ = SOME _’ mp_tac
      \\ simp[Once toFloVerExp_def] \\ rpt strip_tac))
  \\ rveq \\ fs[toRealExp_def, freevars_def]
  \\ rfs[] \\ rveq \\ fs [toRExp_def, toREval_def, eval_expr_cases]
  >- (
    fs[env_sim_def] \\ rveq \\ fs[ExpressionAbbrevsTheory.toRExpMap_def]
    \\ simp[evaluate_def] \\ res_tac \\ fs[v_eq_real])
  >- (
    simp[toRealExp_def, evaluate_def, astTheory.getOpClass_def]
    \\ fs[MachineTypeTheory.mTypeToR_def, perturb_def] \\ rveq
    \\ simp[do_app_def, fp64_to_real_def])
  >- (
    rveq \\ rpt (qpat_x_assum ‘T’ kall_tac)
    \\ fs[freevars_def]
    \\ ‘∃ st2. evaluate st env [toRealExp e] = (st2, Rval [Real v1])’
      by (
        last_x_assum drule \\ rpt (disch_then drule)
        \\ Cases_on ‘m'’ \\ fs[MachineTypeTheory.isCompat_def])
    \\ simp[toRealExp_def, evaluate_def, astTheory.getOpClass_def,
            getRealUop_def]
    \\ ‘st2.fp_state.real_sem’
      by (imp_res_tac fpSemPropsTheory.evaluate_fp_opts_inv)
    \\ fs[do_app_def]
    \\ EVAL_TAC \\ fs[])
  >- (
    imp_res_tac toFloVerExp_ids_unique
    \\ rveq \\ rpt (qpat_x_assum ‘T’ kall_tac)
    \\ fs[freevars_def]
    \\ ‘m1 = REAL ∧ m2 = REAL’
       by (
         conj_tac \\ irule eval_expr_real
         \\ once_rewrite_tac[CONJ_COMM] \\ asm_exists_tac \\ fs[]
         \\ first_x_assum MATCH_ACCEPT_TAC)
    \\ rveq
    \\ ‘∃ st2. evaluate st env [toRealExp e2] = (st2, Rval [Real v2])’
      by (
        last_x_assum drule \\ rpt (disch_then drule)
        \\ disch_then (qspec_then ‘v2’ mp_tac) \\ impl_tac \\ fs[]
        \\ rpt strip_tac
        \\ first_x_assum (qspec_then ‘x’ mp_tac) \\ fs[]
        \\ imp_res_tac toFloVerExp_lookup_mono
        \\ strip_tac \\ fs[]
        \\ res_tac
        \\ fsrw_tac [SATISFY_ss] [])
    \\ ‘st2.fp_state.real_sem’
      by (imp_res_tac fpSemPropsTheory.evaluate_fp_opts_inv)
    \\ ‘∃ st3. evaluate st2 env [toRealExp e1] = (st3, Rval [Real v1])’
      by (
        last_x_assum kall_tac
        \\ last_x_assum drule \\ rpt (disch_then drule)
        \\ disch_then (qspec_then ‘v1’ mp_tac) \\ impl_tac \\ fs[]
        \\ rpt strip_tac
        \\ first_x_assum (qspec_then ‘x’ mp_tac) \\ fs[])
    \\ ‘st3.fp_state.real_sem’
      by (imp_res_tac fpSemPropsTheory.evaluate_fp_opts_inv)
    \\ simp[evaluate_def, astTheory.getOpClass_def, semanticPrimitivesTheory.do_app_def]
    \\ fs[MachineTypeTheory.mTypeToR_def, perturb_def]
    \\ Cases_on ‘bop’ \\ EVAL_TAC)
  >- (
    imp_res_tac toFloVerExp_ids_unique
    \\ rveq \\ rpt (qpat_x_assum ‘T’ kall_tac)
    \\ fs[freevars_def]
    \\ ‘m1 = REAL ∧ m2 = REAL ∧ m3 = REAL’
       by (
         rpt conj_tac \\ irule eval_expr_real
         \\ once_rewrite_tac[CONJ_COMM] \\ asm_exists_tac \\ fs[]
         \\ first_x_assum MATCH_ACCEPT_TAC)
    \\ rveq
    \\ ‘∀ st. st.fp_state.real_sem ⇒ ∃ st2. evaluate st env [toRealExp e3] = (st2, Rval [Real v3])’
      by (
        rpt strip_tac
        \\ last_x_assum drule \\ rpt (disch_then drule)
        \\ disch_then (qspec_then ‘v3’ mp_tac)
        \\ impl_tac \\ fs[]
        \\ rpt strip_tac
        \\ first_x_assum (qspec_then ‘x’ mp_tac) \\ fs[]
        \\ strip_tac
        \\ imp_res_tac toFloVerExp_lookup_mono
        \\ res_tac
        \\ fsrw_tac [SATISFY_ss] [])
    \\ last_x_assum kall_tac
    \\ ‘∀ st. st.fp_state.real_sem ⇒ ∃ st2. evaluate st env [toRealExp e2] = (st2, Rval [Real v2])’
      by (
        rpt strip_tac
        \\ last_x_assum drule \\ rpt (disch_then drule)
        \\ disch_then (qspec_then ‘v2’ mp_tac) \\ impl_tac \\ fs[]
        \\ rpt strip_tac
        \\ first_x_assum (qspec_then ‘x’ mp_tac) \\ fs[]
        \\ imp_res_tac toFloVerExp_lookup_mono
        \\ strip_tac \\ fs[]
        \\ res_tac
        \\ fsrw_tac [SATISFY_ss] [])
    \\ last_x_assum kall_tac
    \\ ‘∀ st. st.fp_state.real_sem ⇒ ∃ st2. evaluate st env [toRealExp e1] = (st2, Rval [Real v1])’
      by (
        rpt strip_tac
        \\ last_x_assum drule \\ rpt (disch_then drule)
        \\ disch_then (qspec_then ‘v1’ mp_tac) \\ impl_tac \\ fs[]
        \\ rpt strip_tac
        \\ first_x_assum (qspec_then ‘x’ mp_tac) \\ fs[]
        \\ imp_res_tac toFloVerExp_lookup_mono
        \\ strip_tac \\ fs[]
        \\ res_tac
        \\ fsrw_tac [SATISFY_ss] [])
    \\ last_x_assum kall_tac
    \\ first_x_assum (qspec_then ‘st’ mp_tac) \\ impl_tac \\ fs[]
    \\ strip_tac \\ fs[]
    \\ ‘st2.fp_state.real_sem’
      by (imp_res_tac fpSemPropsTheory.evaluate_fp_opts_inv)
    \\ last_x_assum (qspec_then ‘st2’ mp_tac) \\ impl_tac \\ fs[]
    \\ strip_tac \\ fs[]
    \\ rename1 ‘evaluate st2 env [toRealExp e3] = (st3, Rval [Real v3])’
    \\ ‘st3.fp_state.real_sem’
      by (imp_res_tac fpSemPropsTheory.evaluate_fp_opts_inv)
    \\ last_x_assum (qspec_then ‘st3’ mp_tac) \\ impl_tac \\ fs[]
    \\ strip_tac \\ fs[]
    \\ rename1 ‘evaluate st3 env [toRealExp e2] = (st4, Rval [Real v2])’
    \\ ‘st4.fp_state.real_sem’
      by (imp_res_tac fpSemPropsTheory.evaluate_fp_opts_inv)
    \\ simp[evaluate_def, astTheory.getOpClass_def,
            semanticPrimitivesTheory.do_app_def]
    \\ simp[evaluateTheory.shift_fp_opts_def]
    \\ fs[MachineTypeTheory.mTypeToR_def, perturb_def]
    \\ EVAL_TAC \\ REAL_ARITH_TAC)
QED

Theorem CakeML_FloVer_real_sim:
  ∀ varMap freshId f theIds freshId2 theCmd E env fVars st Gamma r.
    toFloVerCmd varMap freshId f = SOME (theIds, freshId2, theCmd) ∧
    ids_unique varMap freshId ∧
    st.fp_state.real_sem ∧
    env_sim env.v E fVars Gamma ∧
    (∀ x m. Gamma x = SOME m ⇒ m = REAL) ∧
    (∀ x y. (x,y) IN fVars ⇒ lookupCMLVar x varMap = SOME (x,y)) ∧
    (∀ x. x IN freevars [f] ⇒ ∃ y. lookupCMLVar x varMap = SOME (x,y) ∧ (x,y) IN fVars) ∧
    bstep (toREvalCmd (toRCmd theCmd)) E Gamma r REAL ⇒
    ∃ st2. evaluate st env [toRealExp f] = (st2, Rval [Real r])
Proof
  ho_match_mp_tac toFloVerCmd_ind
  \\ rpt strip_tac \\ fs[toFloVerCmd_def]
  >- (
   fs[option_case_eq, pair_case_eq] \\ rveq
   \\ qpat_x_assum ‘bstep _ _ _ _ _’ mp_tac
   \\ simp[Once toRCmd_def, Once toREvalCmd_def, bstep_cases, freevars_def]
   \\ rpt strip_tac
   \\ drule CakeML_FloVer_real_sim_exp \\ rpt (disch_then drule)
   \\ disch_then (qspec_then ‘v’ mp_tac) \\ impl_tac \\ fs[freevars_def]
   \\ disch_then assume_tac \\ fs[]
   \\ ‘st2.fp_state.real_sem’
      by (imp_res_tac fpSemPropsTheory.evaluate_fp_opts_inv)
   \\ qpat_assum ‘bstep _ _ _ _ _’
                   (fn thm => first_x_assum (fn ithm => mp_then Any mp_tac ithm thm))
   \\ disch_then
      (qspecl_then [‘env with v := (nsOptBind (SOME x) (Real v) env.v)’,
                    ‘fVars UNION { (Short x,freshId2')}’,
                    ‘st2’] mp_tac)
   \\ impl_tac
   >- (
     rpt conj_tac \\ fs[]
     >- (
       irule ids_unique_append
       \\ irule toFloVerExp_ids_unique \\ asm_exists_tac \\ fs[])
     >- (
       simp[env_sim_def] \\ rpt strip_tac \\ fs[namespaceTheory.nsOptBind_def]
       >- (
         ‘cake_id ≠ Short x’
          by (CCONTR_TAC
              \\ fs[] \\ rveq \\ res_tac
              \\ imp_res_tac toFloVerExp_lookup_mono \\ fs[])
         \\ ‘flover_id ≠ freshId2'’
           by (CCONTR_TAC
               \\ fs[] \\ rveq \\ res_tac
               \\ imp_res_tac toFloVerExp_ids_unique
               \\ imp_res_tac toFloVerExp_lookup_mono
               \\ fs[ids_unique_def] \\ res_tac
               \\ fs[])
         \\ fs[env_sim_def] \\ res_tac
         \\ fsrw_tac [SATISFY_ss] []
         \\ res_tac \\ fs[])
       >- (
         ‘cake_id ≠ Short x’
          by (CCONTR_TAC
              \\ fs[] \\ rveq \\ res_tac
              \\ imp_res_tac toFloVerExp_lookup_mono \\ fs[])
         \\ ‘flover_id ≠ freshId2'’
           by (CCONTR_TAC
               \\ fs[] \\ rveq \\ res_tac
               \\ imp_res_tac toFloVerExp_ids_unique
               \\ imp_res_tac toFloVerExp_lookup_mono
               \\ fs[ids_unique_def] \\ res_tac
               \\ fs[])
         \\ fs[ml_progTheory.nsLookup_nsBind_compute]
         \\ fs[env_sim_def] \\ res_tac
         \\ fsrw_tac [SATISFY_ss] []
         \\ res_tac \\ rfs[])
       >- (
         rveq \\ fs[ml_progTheory.nsLookup_nsBind_compute]
         \\ rveq \\ fs[v_eq_def])
       \\ rveq \\ fs[] \\ rveq \\ fs[v_eq_def])
     >- (
      rpt strip_tac
      >- (
        fs[lookupCMLVar_appendCMLVar]
        \\ ‘x' ≠ Short x’
          by (CCONTR_TAC
              \\ fs[] \\ rveq \\ res_tac
              \\ imp_res_tac toFloVerExp_lookup_mono \\ fs[])
         \\ ‘y ≠ freshId2'’
           by (CCONTR_TAC
               \\ fs[] \\ rveq \\ res_tac
               \\ imp_res_tac toFloVerExp_ids_unique
               \\ imp_res_tac toFloVerExp_lookup_mono
               \\ fs[ids_unique_def] \\ res_tac
               \\ fs[])
         \\ res_tac
         \\ imp_res_tac toFloVerExp_lookup_mono
         \\ fs[lookupCMLVar_def, updateTheory.FIND_def])
      \\ rveq \\ fs[lookupCMLVar_appendCMLVar, lookupCMLVar_def, updateTheory.FIND_def])
     >- (
       rpt strip_tac
       \\ fs[lookupCMLVar_appendCMLVar, lookupCMLVar_def, updateTheory.FIND_def]
       \\ TOP_CASE_TAC \\ fs[]
       \\ first_x_assum (qspec_then ‘x'’ mp_tac) \\ fs[]
       \\ disch_then assume_tac \\ fs[]
       \\ imp_res_tac (SIMP_RULE std_ss [lookupCMLVar_def] toFloVerExp_lookup_mono)
       \\ fs[]))
    \\ disch_then assume_tac \\ fs[]
    \\ simp[toRealExp_def, evaluate_def])
  \\ fs[option_case_eq, pair_case_eq] \\ rveq
  \\ fs[Once toRCmd_def, Once toREvalCmd_def, bstep_cases] \\ rveq
  \\ drule CakeML_FloVer_real_sim_exp \\ fs[]
  \\ rpt (disch_then drule) \\ fs[]
QED

Theorem CakeML_FloVer_float_sim_exp:
  ∀ varMap freshId f theIds freshId2 theExp E env fVars st vF Gamma.
    toFloVerExp varMap freshId f = SOME (theIds, freshId2, theExp) ∧
    st.fp_state.canOpt = FPScope NoOpt ∧
    ids_unique varMap freshId ∧
    (∀ x m. (toRExpMap Gamma) x = SOME m ⇒ m = M64) ∧
    (∀ x y. (x,y) IN fVars ⇒ lookupCMLVar x varMap = SOME (x,y)) ∧
    env_sim env.v E fVars (toRExpMap Gamma) ∧
    (∀ x. x IN freevars [f] ⇒ ∃ y. lookupCMLVar x varMap = SOME (x,y) ∧ (x,y) IN fVars) ∧
    validTypes (toRExp theExp) Gamma ∧
    eval_expr_float theExp
      (λ x. case E x of NONE => NONE | SOME v => SOME (float_to_fp64 (round roundTiesToEven v))) =
      SOME vF ⇒
    ∃ vFC st2. evaluate st env [f] = (st2, Rval [vFC]) ∧ v_eq vFC (fp64_to_real vF) M64
Proof
  ho_match_mp_tac toFloVerExp_ind
  \\ rpt strip_tac
  \\ ((rename1 ‘App op exps’ \\ imp_res_tac toFloVerExp_App_cases)
     ORELSE
     (qpat_x_assum ‘toFloVerExp _ _ _ = SOME _’ mp_tac
      \\ simp[Once toFloVerExp_def] \\ rpt strip_tac))
  >- (
    fs[option_case_eq, pair_case_eq] \\ rveq
    \\ fs[eval_expr_float_def, option_case_eq, Once validTypes_def, toRExp_def,
          ExpressionAbbrevsTheory.toRExpMap_def, freevars_def]
    \\ rveq \\ fs[env_sim_def]
    \\ res_tac \\ rveq \\ fs[] \\ rveq
    \\ simp[evaluate_def]
    \\ Cases_on ‘v'’ \\ fs[v_eq_def] \\ rveq
    >- (
      Cases_on ‘l’ \\ fs[v_eq_def] \\ rveq
      \\ simp[fp64_to_real_def]
      \\ ‘float_is_finite (fp64_to_float c) ∧ ~ float_is_zero (fp64_to_float c)’
        by (cheat)
      \\ fs[lift_ieeeTheory.round_finite_normal_float_id,
            float_to_fp64_fp64_to_float])
    >- (
      ‘float_is_finite (fp64_to_float (compress_word f)) ∧
          ~ float_is_zero (fp64_to_float (compress_word f))’
        by (cheat)
      \\ simp[fp64_to_real_def]
      \\ fs[lift_ieeeTheory.round_finite_normal_float_id,
            float_to_fp64_fp64_to_float]))
  >- (
    fs[option_case_eq, pair_case_eq] \\ rveq
    \\ fs[eval_expr_float_def, option_case_eq, Once validTypes_def, toRExp_def,
          ExpressionAbbrevsTheory.toRExpMap_def, freevars_def]
    \\ rveq \\ fs[]
    \\ simp[evaluate_def, v_eq_def])
  >- (
    fs[option_case_eq, pair_case_eq] \\ rveq
    \\ rpt (qpat_x_assum ‘T’ kall_tac)
    \\ fs[eval_expr_float_def, option_case_eq, toRExp_def,
          ExpressionAbbrevsTheory.toRExpMap_def, freevars_def]
    \\ rveq \\ fs[]
    \\ ‘validTypes (toRExp fexp2) Gamma’
       by (fs[Once validTypes_def])
    \\ ‘∃ vFC st2. evaluate st env [e] = (st2, Rval [vFC]) ∧
        v_eq vFC (fp64_to_real v) M64’
      by (
        last_x_assum drule \\ rpt (disch_then drule)
        \\ disch_then assume_tac \\ fs[])
    \\ ‘st2.fp_state.canOpt = FPScope NoOpt’
       by (imp_res_tac fpSemPropsTheory.evaluate_fp_opts_inv \\ fs[])
    \\ simp[evaluate_def, v_eq_def, astTheory.getOpClass_def, semanticPrimitivesTheory.do_app_def]
    \\ Cases_on ‘vFC’ \\ fs[v_eq_def]
    THENL [Cases_on ‘l’, ALL_TAC]
    \\ fs[v_eq_def, semanticPrimitivesTheory.fp_translate_def,
          astTheory.isFpBool_def, fpValTreeTheory.fp_uop_def,
          fpSemTheory.compress_word_def]
    >- (
      EVAL_TAC
      \\ fs[fp64_to_real_def, fp64_negate_def, fp64_to_float_float_to_fp64,
            binary_ieeeTheory.float_to_real_negate])
    \\ fs[fp64_to_real_def, binary_ieeeTheory.float_to_real_eq]
    >- (
      EVAL_TAC
      \\ fs[fp64_negate_def, fp64_to_float_float_to_fp64])
    \\ EVAL_TAC
    \\ fs[fp64_negate_def, fp64_to_float_float_to_fp64, binary_ieeeTheory.float_to_real_negate]
    \\ fs[binary_ieeeTheory.float_negate_def, binary_ieeeTheory.float_is_zero])
  >- (
    rveq \\ fs[]
    \\ rpt (qpat_x_assum ‘T’ kall_tac)
    \\ fs[eval_expr_float_def, option_case_eq, toRExp_def,
          ExpressionAbbrevsTheory.toRExpMap_def, freevars_def]
    \\ rveq \\ fs[]
    \\ ‘validTypes (toRExp fexp1) Gamma’
       by (fs[Once validTypes_def])
    \\ ‘validTypes (toRExp fexp2) Gamma’
       by (fs[Once validTypes_def])
    \\ ‘∀ x y. (x,y) IN fVars ⇒ lookupCMLVar x theIds2 = SOME (x,y)’
       by (rpt strip_tac \\ res_tac \\ imp_res_tac toFloVerExp_lookup_mono)
    \\ ‘∃ vFC st2. evaluate st env [e2] = (st2, Rval [vFC]) ∧
        v_eq vFC (fp64_to_real v2) M64’
      by (
        imp_res_tac toFloVerExp_ids_unique
        \\ last_x_assum drule \\ rpt (disch_then drule)
        \\ disch_then (qspec_then ‘v2’ mp_tac) \\ impl_tac \\ fs[]
        >- (
          rpt strip_tac \\ ntac 2 (first_x_assum (qspec_then ‘x’ mp_tac)) \\ fs[]
          \\ rpt strip_tac
          \\ imp_res_tac toFloVerExp_lookup_mono \\ fs[])
        \\ disch_then assume_tac \\ fs[])
    \\ ‘st2.fp_state.canOpt = FPScope NoOpt’
      by (imp_res_tac fpSemPropsTheory.evaluate_fp_opts_inv \\ fs[])
    \\ last_x_assum kall_tac
    \\ ‘∃ vFC st3. evaluate st2 env [e1] = (st3, Rval [vFC]) ∧
        v_eq vFC (fp64_to_real v1) M64’
      by (
        imp_res_tac toFloVerExp_ids_unique
        \\ last_x_assum drule \\ rpt (disch_then drule)
        \\ disch_then (qspec_then ‘v1’ mp_tac) \\ impl_tac \\ fs[])
    \\ ‘st3.fp_state.canOpt = FPScope NoOpt’
      by (imp_res_tac fpSemPropsTheory.evaluate_fp_opts_inv \\ fs[])
    \\ simp[evaluate_def, v_eq_def, astTheory.getOpClass_def,
            semanticPrimitivesTheory.do_app_def]
    \\ Cases_on ‘vFC'’ \\ Cases_on ‘vFC’
    \\ TRY (rename1 ‘v_eq (Litv l1) (fp64_to_real v1) M64’ \\ Cases_on ‘l1’)
    \\ TRY (rename1 ‘v_eq (Litv l2) (fp64_to_real v2) M64’ \\ Cases_on ‘l2’)
    \\ fs[v_eq_def, semanticPrimitivesTheory.fp_translate_def,
          astTheory.isFpBool_def, fpValTreeTheory.fp_uop_def,
          fpSemTheory.compress_word_def]
     (* MARKER *)
    \\ fs[fp64_to_real_def, binary_ieeeTheory.float_to_real_eq]
    \\ Cases_on ‘bop’ \\ fs[fpBopToFloVer_def] \\ rveq
    \\ fs[fpSemTheory.compress_word_def, fpValTreeTheory.fp_bop_def]
    \\ EVAL_TAC
    \\ fs[dmode_def, fp64_add_def, fp64_sub_def, fp64mul_def, fp64_div_def]
    \\ qpat_x_assum ‘float_is_zero (fp64_to_float v1)’ (fn thm => assume_tac (SIMP_RULE std_ss [binary_ieeeTheory.float_is_zero] thm) \\ assume_tac thm)
    \\ qpat_x_assum ‘float_is_zero (fp64_to_float c)’ (fn thm => assume_tac (SIMP_RULE std_ss [binary_ieeeTheory.float_is_zero] thm) \\ assume_tac thm)
    \\ fs[binary_ieeeTheory.float_is_zero_def, binary_ieeeTheory.float_add_def]
    \\ Cases_on ‘float_value (fp64_to_float c)’
    \\ Cases_on ‘float_value (fp64_to_float v1)’
    \\ fs[]
    \\ Cases_on ‘float_value (fp64_to_float c')’ \\ fs[fp64_to_float_float_to_fp64] \\ rveq
    \\ cheat

Theorem CakeML_FloVer_float_sim:
  ∀ varMap freshId f theIds freshId2 theCmd E env fVars st vF Gamma.
  toFloVerCmd varMap freshId f = SOME (theIds, freshId2, theCmd) ∧
  ids_unique varMap freshId ∧
  (∀ x m. Gamma x = SOME m ⇒ m = M64) ∧
  (∀ x y. (x,y) IN fVars ⇒ lookupCMLVar x varMap = SOME (x,y)) ∧
  env_sim env.v E fVars Gamma ∧
  (∀ x. x IN freevars [f] ⇒ ∃ y. lookupCMLVar x varMap = SOME (x,y) ∧ (x,y) IN fVars) ∧
  bstep_float theCmd
    (λ x. case E x of NONE => NONE | SOME v => SOME (float_to_fp64 (round roundTiesToEven v))) =
    SOME vF ⇒
  ∃ st2. evaluate st env [toRealExp f] = (st2, Rval [FP_WordTree (Fp_const vF)])
Proof
  cheat
QED

Theorem CakeML_FloVer_infer_error:
  ∀ (st st2:'a semanticPrimitives$state) env Gamma P analysisResult
    decl ids cake_P f floverVars varMap freshId freshId2 theIds theCmd dVars E fVars.
  (* the CakeML code can be translated into FloVer input *)
  prepareKernel (getFunctions decl) = SOME (ids, cake_P, f) ∧
  prepareVars ids = (floverVars, varMap, freshId) ∧
  Gamma = prepareGamma floverVars ∧
  toFloVerCmd varMap freshId f = SOME (theIds, freshId2, theCmd) ∧
  toFloVerPre [cake_P] varMap = SOME (P, dVars) ∧
  computeErrorbounds theCmd P Gamma = SOME analysisResult ∧
  evaluate st env [cake_P] = (st2, Rval [Boolv T]) ∧
  (∀ x. x IN freevars [f] ⇒ x IN freevars [cake_P]) ∧
  st.fp_state.canOpt = FPScope NoOpt ∧
  (* the free variables are paired up in the id list, and defined *)
  env_sim env.v E fVars (toRExpMap Gamma) ∧
  (∀ x. x IN freevars [cake_P] ⇔ x IN freevars [f]) (* TODO: Should this be checked? *) ∧
  (∀ x. x IN freevars [cake_P] ⇒ ∃ y. lookupCMLVar x varMap = SOME (x,y) ∧ (x,y) IN fVars) ==>
  ∃ ids iv err st3 w st4 r.
    (* the analysis result returned contains an error bound *)
    FloverMapTree_find (getRetExp (toRCmd theCmd)) analysisResult = SOME (iv,err) /\
    (* we can evaluate with a real-valued semantics *)
    evaluate st env [toRealExp f] = (st3, Rval [Real r]) /\
    (* the CakeML code returns a valid floating-point word *)
    evaluate st env [f] = (st4, Rval [FP_WordTree w]) /\
    (* the roundoff error is sound *)
    real$abs (fp64_to_real (compress_word w) - r)
      <= err
Proof
  rpt strip_tac \\ imp_res_tac prepareVars_is_unique
  \\ rveq
  \\ first_assum (mp_then Any assume_tac toFloVerPre_preserves_bounds)
  (* the free variables of the program are bound and sound with respect to P *)
  \\ qpat_x_assum ‘computeErrorbounds _ _ _ = _’ mp_tac
  \\ simp[computeErrorbounds_def]
  \\ ntac 4 (TOP_CASE_TAC \\ fs[])
  \\ rpt strip_tac \\ fs[] \\ rveq
  \\ imp_res_tac CertificateCheckerCmd_Gamma_is_getValidMapCmd
  \\ fs[] \\ rveq
  \\ imp_res_tac IEEE_connectionTheory.IEEE_connection_cmds
  (* Issue 1: We need to somehow disallow underflow here... *)
  \\ first_x_assum
     (qspecl_then
      [ ‘λ x. case E x of |SOME v => SOME (float_to_fp64 (round roundTiesToEven v)) | NONE => NONE’,
        ‘E’]
      mp_tac)
  \\ impl_tac
  >- (
    irule approxEnv_construct \\ rpt conj_tac
    (* Assumption that we do not run into subnormal nums *)
    >- (cheat)
    (* assumption from env simulation *)
    >- (cheat)
    (* assumption from env simulation ? *)
    >- (cheat)
    (* invariant of construction of Gamma *)
    \\ rpt strip_tac
    \\ rename1 ‘y IN domain (freeVars (toRCmd theCmd))’
    \\ ‘y IN domain (freeVars theCmd)’ by fs[toRCmd_freeVars_agree]
    \\ simp[ExpressionAbbrevsTheory.toRExpMap_def]
    \\ qspec_then ‘floverVars’ assume_tac is64BitEnv_prepareGamma
    \\ fs[is64BitEnv_def]
    \\ imp_res_tac getValidMapCmd_preserving
    \\ cheat) (* TODO *)
       (*
    \\ irule getValidMapCmd_is_64Bit

    \\ asm_exists_tac \\ fs[]
    \\ qexists_tac ‘FloverMapTree_empty’ \\ fs[FloverMapTree_empty_def, is64BitEnv_def, FloverMapTree_find_def]
    \\ asm_exists_tac \\ fs[]) *)
  (* TODO: Should this be free vars + domain of Precondition/function parameters? *)
  \\ disch_then (qspec_then ‘freeVars (toRCmd theCmd)’ mp_tac)
  \\ impl_tac \\ fs[]
  \\ impl_tac
  >- (
    simp[RealRangeArithTheory.fVars_P_sound_def]
    \\ rpt strip_tac
    \\ first_x_assum irule \\ fs[PULL_EXISTS]
    \\ qexists_tac ‘toRExpMap (prepareGamma floverVars)’ \\ qexists_tac  ‘[cake_P]’ \\ fs[]
    \\ qexists_tac ‘env’
    \\ rewrite_tac [CONJ_ASSOC]
    \\ once_rewrite_tac [CONJ_COMM]
    \\ asm_exists_tac \\ fs[]
    \\ qexists_tac ‘st’ \\ qexists_tac ‘st2’ \\ fs[]
    \\ imp_res_tac toRCmd_freeVars_agree
    \\ drule toFloVerCmd_freevars_agree \\ fs[]
    \\ disch_then imp_res_tac \\ fs[]
    \\ ‘x' IN freevars [cake_P]’ by fs[]
    \\ first_x_assum (qspec_then ‘x'’ assume_tac)
    \\ res_tac
    \\ ‘lookupFloVerVar y varMap = SOME (x', y)’ by fs[ids_unique_def]
    \\ imp_res_tac toFloVerCmd_lookup_mono
    \\ ‘lookupFloVerVar y theIds = SOME (x', y)’ by fs[ids_unique_def]
    \\ imp_res_tac toFloVerCmd_ids_unique
    \\ ‘y = v’ by (fs[ids_unique_def])
    \\ rveq \\ fs[])
  \\ impl_tac
  (* Can only be done once we know which environment to pick for the subnormal evaluation*)
  >- (cheat) (* TODO: bstep_valid *)
  \\ impl_tac
  (* invariant of the translation to FloVer: noDowncastFun is true *)
  >- (
    irule toFloVerCmd_noDowncastFun
    \\ asm_exists_tac \\ fs[])
  \\ impl_tac
  (* invariant of prepareVars: is64BitEnv (prepareGamma floverVars) *)
  >- (irule is64BitEnv_prepareGamma)
  \\ impl_tac
  (* invariant of translation to FloVer: is64BitBstep (toRCmd theCmd) *)
  >- (
    irule toFloVerCmd_is64BitBstep
    \\ asm_exists_tac \\ fs[])
  \\ disch_then assume_tac \\ fs[]
  (* Simulation 1: We can get the same result as the FloVer reals from CakeML reals *)
  \\ ‘∃ st3. evaluate st env [toRealExp f] = (st3, Rval [Real vR'])’
     by (cheat) (* TODO: Change assumptions *)
     (* by (drule CakeML_FloVer_real_sim
         \\ disch_then drule
         \\ disch_then (qspecl_then [‘st’, ‘a’, ‘vR'’] mp_tac)
         \\ impl_tac \\ fs[]) *)
  (* Simulation 2: We can get the same result as FloVer floats for CakeML *)
  \\ ‘evaluate st env [f] = (st2, Rval [FP_WordTree (Fp_const vF)])’
     by (cheat) (* TODO: Change assumptions *)
        (*
     by (drule CakeML_FloVer_float_sim
         \\ disch_then drule
         \\ disch_then (qspecl_then [‘st’, ‘vF’] mp_tac)
         \\ impl_tac \\ fs[]) *)
  \\ fsrw_tac [SATISFY_ss] [fpSemTheory.compress_word_def]
  \\ once_rewrite_tac [ABS_SUB]
  \\ simp[fp64_to_real_def]
QED

val _ = export_theory ();
