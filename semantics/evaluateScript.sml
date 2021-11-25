(*
  Functional big-step semantics for evaluation of CakeML programs.
*)
open HolKernel Parse boolLib bossLib;
open libTheory astTheory namespaceTheory ffiTheory semanticPrimitivesTheory;

val _ = numLib.prefer_num();

val _ = new_theory "evaluate"

(* The semantics is defined here using fix_clock so that HOL4 generates
 * provable termination conditions. However, after termination is proved, we
 * clean up the definition (in HOL4) to remove occurrences of fix_clock. *)

val _ = Define `
 ((fix_clock:'a state -> 'b state#'c -> 'b state#'c) s (s',res)=
   (( s' with<| clock := (if s'.clock <= s.clock
                     then s'.clock else s.clock) |>),res))`;


val _ = Define `
 ((dec_clock:'a state -> 'a state) s=  (( s with<| clock := (s.clock -( 1 : num)) |>)))`;


val _ = Define `
 ((do_eval_res:(v)list -> 'b state -> 'b state#(((v)sem_env#(dec)list),'a)result) vs s=  ((case do_eval vs s.eval_state of
    NONE => (s, Rerr (Rabort Rtype_error))
  | SOME (env1, decs, es1) => (( s with<| eval_state := es1 |>), Rval (env1, decs))
  )))`;


(* list_result is equivalent to map_result (\v. [v]) I, where map_result is
 * defined in evalPropsTheory *)
 val _ = Define `

((list_result:('a,'b)result ->(('a list),'b)result) (Rval v)=  (Rval [v]))
/\
((list_result:('a,'b)result ->(('a list),'b)result) (Rerr e)=  (Rerr e))`;


(*val evaluate : forall 'ffi. state 'ffi -> sem_env v -> list exp -> state 'ffi * result (list v) v*)
(*val evaluate_match : forall 'ffi. state 'ffi -> sem_env v -> v -> list (pat * exp) -> v -> state 'ffi * result (list v) v*)
(*val evaluate_decs : forall 'ffi. state 'ffi -> sem_env v -> list dec -> state 'ffi * result (sem_env v) v*)
 val evaluate_defn = Defn.Hol_multi_defns `

((evaluate:'ffi state ->(v)sem_env ->(exp)list -> 'ffi state#(((v)list),(v))result) st env []=  (st, Rval []))
/\
((evaluate:'ffi state ->(v)sem_env ->(exp)list -> 'ffi state#(((v)list),(v))result) st env (e1::e2::es)=
   ((case fix_clock st (evaluate st env [e1]) of
    (st', Rval v1) =>
      (case evaluate st' env (e2::es) of
        (st'', Rval vs) => (st'', Rval (HD v1::vs))
      | res => res
      )
  | res => res
  )))
/\
((evaluate:'ffi state ->(v)sem_env ->(exp)list -> 'ffi state#(((v)list),(v))result) st env [Lit l]=  (st, Rval [Litv l]))
/\
((evaluate:'ffi state ->(v)sem_env ->(exp)list -> 'ffi state#(((v)list),(v))result) st env [Raise e]=
   ((case evaluate st env [e] of
    (st', Rval v) => (st', Rerr (Rraise (HD v)))
  | res => res
  )))
/\
((evaluate:'ffi state ->(v)sem_env ->(exp)list -> 'ffi state#(((v)list),(v))result) st env [Handle e pes]=
   ((case fix_clock st (evaluate st env [e]) of
    (st', Rerr (Rraise v)) =>
      if can_pmatch_all env.c st'.refs (MAP FST pes) v
      then evaluate_match st' env v pes v
      else (st', Rerr (Rabort Rtype_error))
  | res => res
  )))
/\
((evaluate:'ffi state ->(v)sem_env ->(exp)list -> 'ffi state#(((v)list),(v))result) st env [Con cn es]=
   (if do_con_check env.c cn (LENGTH es) then
    (case evaluate st env (REVERSE es) of
      (st', Rval vs) =>
        (case build_conv env.c cn (REVERSE vs) of
          SOME v => (st', Rval [v])
        | NONE => (st', Rerr (Rabort Rtype_error))
        )
    | res => res
    )
  else (st, Rerr (Rabort Rtype_error))))
/\
((evaluate:'ffi state ->(v)sem_env ->(exp)list -> 'ffi state#(((v)list),(v))result) st env [Var n]=
   ((case nsLookup env.v n of
    SOME v => (st, Rval [v])
  | NONE => (st, Rerr (Rabort Rtype_error))
  )))
/\
((evaluate:'ffi state ->(v)sem_env ->(exp)list -> 'ffi state#(((v)list),(v))result) st env [Fun x e]=  (st, Rval [Closure env x e]))
/\
((evaluate:'ffi state ->(v)sem_env ->(exp)list -> 'ffi state#(((v)list),(v))result) st env [App op es]=
   ((case fix_clock st (evaluate st env (REVERSE es)) of
    (st', Rval vs) =>
      if op = Opapp then
        (case do_opapp (REVERSE vs) of
          SOME (env',e) =>
            if st'.clock =( 0 : num) then
              (st', Rerr (Rabort Rtimeout_error))
            else
              evaluate (dec_clock st') env' [e]
        | NONE => (st', Rerr (Rabort Rtype_error))
        )
      else if op = Eval then
        (case fix_clock st' (do_eval_res (REVERSE vs) st') of
          (st1, Rval (env1, decs)) =>
            if st1.clock =( 0 : num) then
              (st1, Rerr (Rabort Rtimeout_error))
            else
              (case fix_clock (dec_clock st1)
                      (evaluate_decs (dec_clock st1) env1 decs) of
                (st2, Rval env2) => (case declare_env st2.eval_state
                  (extend_dec_env env2 env1) of
                  SOME (x, es2) => (( st2 with<| eval_state :=
                    (reset_env_generation st'.eval_state es2) |>), Rval [x])
                | NONE => (st2, Rerr (Rabort Rtype_error))
                )
              | (st2, Rerr (Rabort a)) => (st2, Rerr (Rabort a))
              | (st2, Rerr e) => (( st2 with<| eval_state :=
                  (reset_env_generation st'.eval_state st2.eval_state) |>), Rerr e)
              )
        | (st1, Rerr e) => (st1, Rerr e)
        )
      else
        (case do_app (st'.refs,st'.ffi) op (REVERSE vs) of
          SOME ((refs,ffi),r) => (( st' with<| refs := refs; ffi := ffi |>), list_result r)
        | NONE => (st', Rerr (Rabort Rtype_error))
        )
  | res => res
  )))
/\
((evaluate:'ffi state ->(v)sem_env ->(exp)list -> 'ffi state#(((v)list),(v))result) st env [Log lop e1 e2]=
   ((case fix_clock st (evaluate st env [e1]) of
    (st', Rval v1) =>
      (case do_log lop (HD v1) e2 of
        SOME (Exp e) => evaluate st' env [e]
      | SOME (Val v) => (st', Rval [v])
      | NONE => (st', Rerr (Rabort Rtype_error))
      )
  | res => res
  )))
/\
((evaluate:'ffi state ->(v)sem_env ->(exp)list -> 'ffi state#(((v)list),(v))result) st env [If e1 e2 e3]=
   ((case fix_clock st (evaluate st env [e1]) of
    (st', Rval v) =>
      (case do_if (HD v) e2 e3 of
        SOME e => evaluate st' env [e]
      | NONE => (st', Rerr (Rabort Rtype_error))
      )
  | res => res
  )))
/\
((evaluate:'ffi state ->(v)sem_env ->(exp)list -> 'ffi state#(((v)list),(v))result) st env [Mat e pes]=
   ((case fix_clock st (evaluate st env [e]) of
    (st', Rval v) =>
      if can_pmatch_all env.c st'.refs (MAP FST pes) (HD v)
      then evaluate_match st' env (HD v) pes bind_exn_v
      else (st', Rerr (Rabort Rtype_error))
  | res => res
  )))
/\
((evaluate:'ffi state ->(v)sem_env ->(exp)list -> 'ffi state#(((v)list),(v))result) st env [Let xo e1 e2]=
   ((case fix_clock st (evaluate st env [e1]) of
    (st', Rval v) => evaluate st' ( env with<| v := (nsOptBind xo (HD v) env.v) |>) [e2]
  | res => res
  )))
/\
((evaluate:'ffi state ->(v)sem_env ->(exp)list -> 'ffi state#(((v)list),(v))result) st env [Letrec funs e]=
   (if ALL_DISTINCT (MAP (\ (x,y,z) .  x) funs) then
    evaluate st ( env with<| v := (build_rec_env funs env env.v) |>) [e]
  else
    (st, Rerr (Rabort Rtype_error))))
/\
((evaluate:'ffi state ->(v)sem_env ->(exp)list -> 'ffi state#(((v)list),(v))result) st env [Tannot e t]=
   (evaluate st env [e]))
/\
((evaluate:'ffi state ->(v)sem_env ->(exp)list -> 'ffi state#(((v)list),(v))result) st env [Lannot e l]=
   (evaluate st env [e]))
/\
((evaluate_match:'ffi state ->(v)sem_env -> v ->(pat#exp)list -> v -> 'ffi state#(((v)list),(v))result) st env v [] err_v=  (st, Rerr (Rraise err_v)))
/\
((evaluate_match:'ffi state ->(v)sem_env -> v ->(pat#exp)list -> v -> 'ffi state#(((v)list),(v))result) st env v ((p,e)::pes) err_v=
    (if ALL_DISTINCT (pat_bindings p []) then
    (case pmatch env.c st.refs p v [] of
      Match env_v' => evaluate st ( env with<| v := (nsAppend (alist_to_ns env_v') env.v) |>) [e]
    | No_match => evaluate_match st env v pes err_v
    | Match_type_error => (st, Rerr (Rabort Rtype_error))
    )
  else (st, Rerr (Rabort Rtype_error))))
/\
((evaluate_decs:'ffi state ->(v)sem_env ->(dec)list -> 'ffi state#(((v)sem_env),(v))result) st env []=  (st, Rval <| v := nsEmpty; c := nsEmpty |>))
/\
((evaluate_decs:'ffi state ->(v)sem_env ->(dec)list -> 'ffi state#(((v)sem_env),(v))result) st env (d1::d2::ds)=
   ((case fix_clock st (evaluate_decs st env [d1]) of
    (st1, Rval env1) =>
    (case evaluate_decs st1 (extend_dec_env env1 env) (d2::ds) of
      (st2,r) => (st2, combine_dec_result env1 r)
    )
  | res => res
  )))
/\
((evaluate_decs:'ffi state ->(v)sem_env ->(dec)list -> 'ffi state#(((v)sem_env),(v))result) st env [Dlet locs p e]=
   (if ALL_DISTINCT (pat_bindings p []) then
    (case evaluate st env [e] of
      (st', Rval v) =>
        (st',
         (case pmatch env.c st'.refs p (HD v) [] of
           Match new_vals => Rval <| v := (alist_to_ns new_vals); c := nsEmpty |>
         | No_match => Rerr (Rraise bind_exn_v)
         | Match_type_error => Rerr (Rabort Rtype_error)
         ))
    | (st', Rerr err) => (st', Rerr err)
    )
  else
    (st, Rerr (Rabort Rtype_error))))
/\
((evaluate_decs:'ffi state ->(v)sem_env ->(dec)list -> 'ffi state#(((v)sem_env),(v))result) st env [Dletrec locs funs]=
   (st,
   (if ALL_DISTINCT (MAP (\ (x,y,z) .  x) funs) then
     Rval <| v := (build_rec_env funs env nsEmpty); c := nsEmpty |>
   else
     Rerr (Rabort Rtype_error))))
/\
((evaluate_decs:'ffi state ->(v)sem_env ->(dec)list -> 'ffi state#(((v)sem_env),(v))result) st env [Dtype locs tds]=
   (if EVERY check_dup_ctors tds then
    (( st with<| next_type_stamp := (st.next_type_stamp + LENGTH tds) |>),
     Rval <| v := nsEmpty; c := (build_tdefs st.next_type_stamp tds) |>)
  else
    (st, Rerr (Rabort Rtype_error))))
/\
((evaluate_decs:'ffi state ->(v)sem_env ->(dec)list -> 'ffi state#(((v)sem_env),(v))result) st env [Dtabbrev locs tvs tn t]=
   (st, Rval <| v := nsEmpty; c := nsEmpty |>))
/\
((evaluate_decs:'ffi state ->(v)sem_env ->(dec)list -> 'ffi state#(((v)sem_env),(v))result) st env [Denv n]=
   ((case declare_env st.eval_state env of
    SOME (x, es') => (( st with<| eval_state := es' |>),
        Rval <| v := (nsSing n x); c := nsEmpty |>)
  | NONE => (st, Rerr (Rabort Rtype_error))
  )))
/\
((evaluate_decs:'ffi state ->(v)sem_env ->(dec)list -> 'ffi state#(((v)sem_env),(v))result) st env [Dexn locs cn ts]=
   (( st with<| next_exn_stamp := (st.next_exn_stamp +( 1 : num)) |>),
   Rval <| v := nsEmpty; c := (nsSing cn (LENGTH ts, ExnStamp st.next_exn_stamp)) |>))
/\
((evaluate_decs:'ffi state ->(v)sem_env ->(dec)list -> 'ffi state#(((v)sem_env),(v))result) st env [Dmod mn ds]=
   ((case evaluate_decs st env ds of
    (st', r) =>
      (st',
       (case r of
         Rval env' => Rval <| v := (nsLift mn env'.v); c := (nsLift mn env'.c) |>
       | Rerr err => Rerr err
       ))
  )))
/\
((evaluate_decs:'ffi state ->(v)sem_env ->(dec)list -> 'ffi state#(((v)sem_env),(v))result) st env [Dlocal lds ds]=
   ((case fix_clock st (evaluate_decs st env lds) of
    (st1, Rval env1) =>
    evaluate_decs st1 (extend_dec_env env1 env) ds
  | res => res
  )))`;

val _ = Lib.with_flag (computeLib.auto_import_definitions, false) (List.map Defn.save_defn) evaluate_defn;
val _ = export_theory()
