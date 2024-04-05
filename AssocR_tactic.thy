(* *********************************************************************

    Theory AssocR_tactic.thy is part of a framework for modelling,
    verification and transformation of concurrent imperative
    programs. Copyright (c) 2021  M. Bortin

    The framework is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.
    For more details see the license agreement (LICENSE) you should have
    received along with the framework.
    
   ******************************************************************* *)

theory AssocR_tactic
imports ProgCorr 
begin

lemma small_step_eqv_seqs :
"\<rho>, \<rho>' \<Turnstile> p \<approx> p' \<Longrightarrow> \<rho>, \<rho>' \<Turnstile> q \<approx> q' \<Longrightarrow>
 \<rho>, \<rho>' \<Turnstile> p;q \<approx> (p';q')"
  apply(simp add: small_step_eqv)
  apply clarify
  apply(rule conjI)
   apply(erule prog_corr_seqs, assumption)+
  done


lemma small_step_eqv_conds :
"\<rho>, \<rho>' \<Turnstile> p \<approx> p' \<Longrightarrow>
 \<rho>, \<rho>' \<Turnstile> q \<approx> q' \<Longrightarrow>
 \<rho>, \<rho>' \<Turnstile> Cond C p q \<approx> Cond C p' q'"
  apply(simp add: small_step_eqv)
  apply clarify
  apply(rule conjI)
   apply(erule prog_corr_conds, assumption, clarsimp)+
  done

lemma small_step_eqv_whiles :
"\<rho>, \<rho>' \<Turnstile> p \<approx> p' \<Longrightarrow>
 \<rho>, \<rho>' \<Turnstile> q \<approx> q' \<Longrightarrow>
 \<rho>, \<rho>' \<Turnstile> While C I p q \<approx> While C I' p' q'"
  apply(simp add: small_step_eqv)
  apply clarify
  apply(rule conjI)
   apply(erule prog_corr_whiles, assumption, clarsimp)+
  done


lemma small_step_eqv_parallels' :
"(\<And>i. i < length ps \<Longrightarrow> \<rho>, \<rho>' \<Turnstile> fst (ps ! i) \<approx> fst (ps' ! i)) \<Longrightarrow>
 length ps = length ps' \<Longrightarrow>
  \<rho>, \<rho>' \<Turnstile> Parallel ps \<approx> Parallel ps'"
  apply(simp add: small_step_eqv)
  apply(rule conjI)
   apply(rule prog_corr_parallels', fastforce, assumption)
  apply(rule prog_corr_parallels', fastforce, simp)
  done


lemma small_step_eqv_parallels2 :
"\<rho>, \<rho>' \<Turnstile> fst p1 \<approx> fst q1 \<Longrightarrow>
 \<rho>, \<rho>' \<Turnstile> fst p2 \<approx> fst q2 \<Longrightarrow>
  \<rho>, \<rho>' \<Turnstile> Parallel [p1, p2] \<approx> Parallel [q1, q2]"
  by(rule small_step_eqv_parallels', case_tac i, simp+)

lemma small_step_eqv_parallels3 :
"\<rho>, \<rho>' \<Turnstile> fst p1 \<approx> fst q1 \<Longrightarrow>
 \<rho>, \<rho>' \<Turnstile> fst p2 \<approx> fst q2 \<Longrightarrow>
 \<rho>, \<rho>' \<Turnstile> fst p3 \<approx> fst q3 \<Longrightarrow>
  \<rho>, \<rho>' \<Turnstile> Parallel [p1, p2, p3] \<approx> Parallel [q1, q2, q3]"
  apply(rule small_step_eqv_parallels', case_tac i, simp+)
   apply(rename_tac n, case_tac n, simp+)
  done

lemma small_step_eqv_scheme :
"(\<And>i. n \<le> i \<Longrightarrow> i < m \<Longrightarrow> \<rho>, \<rho>' \<Turnstile> fst (f i) \<approx> fst (g i)) \<Longrightarrow>
  \<rho>, \<rho>' \<Turnstile> Parallel (map f [n..<m]) \<approx> Parallel (map g [n..<m])"
  by(rule small_step_eqv_parallels', case_tac i, simp+)

lemma small_step_eqv_substL' :
"\<rho> \<Turnstile> p' \<approx> p \<Longrightarrow> \<rho>, \<rho>' \<Turnstile> p \<sqsupseteq>\<^bsub>r\<^esub> p'' \<Longrightarrow>
 \<rho>, \<rho>' \<Turnstile> p' \<sqsupseteq>\<^bsub>r\<^esub> p''"
  apply(rule small_step_eqv_substL, assumption)
  apply(erule small_step_eqv_sym)
  done

lemma small_step_eqv_substR' :
"\<rho>' \<Turnstile> p' \<approx> p'' \<Longrightarrow> \<rho>, \<rho>' \<Turnstile> p \<sqsupseteq>\<^bsub>r\<^esub> p'' \<Longrightarrow>
 \<rho>, \<rho>' \<Turnstile> p \<sqsupseteq>\<^bsub>r\<^esub> p'"
  apply(rule small_step_eqv_substR, assumption)
  apply(erule small_step_eqv_sym)
  done

lemma RG_subst :
"\<rho> \<Turnstile> p \<approx> p' \<Longrightarrow> \<rho> \<Turnstile> {R, P} p' {Q, G} \<Longrightarrow>
 \<rho> \<Turnstile> {R, P} p {Q, G}"
  by(simp add: prog_corr_RG_eq)


ML \<open>

fun assoc_entryL_tac ctxt = rt ctxt (@{thm small_step_eqv_substL'})
fun assoc_entryR_tac ctxt = rt ctxt (@{thm small_step_eqv_substR'})
fun assoc_entryRG_tac ctxt = rt ctxt (@{thm RG_subst})

fun assoc_app_tac ctxt i =
 FIRST[rt ctxt (@{thm small_step_eqv_trans}) i THEN rt ctxt (@{thm small_step_eqv_seq_assoc}) i,
       rt ctxt (@{thm small_step_eqv_seqs}) i,
       rt ctxt (@{thm small_step_eqv_whiles}) i,
       rt ctxt (@{thm small_step_eqv_conds}) i,
       rt ctxt (@{thm small_step_eqv_parallels2}) i,
       rt ctxt (@{thm small_step_eqv_parallels3}) i,
       rt ctxt (@{thm small_step_eqv_scheme}) i]


fun assocLHS_tac ctxt =
 SUBGOAL (fn (_, i) => assoc_entryL_tac ctxt i
 THEN REPEAT_ALL_NEW (assoc_app_tac ctxt) i THEN TRYALL (rt ctxt (@{thm small_step_eqv_refl})))

fun assocRHS_tac ctxt =
 SUBGOAL (fn (_, i) => assoc_entryR_tac ctxt i
 THEN REPEAT_ALL_NEW (assoc_app_tac ctxt) i THEN TRYALL (rt ctxt (@{thm small_step_eqv_refl})))

fun assocRG_tac ctxt =
 SUBGOAL (fn (_, i) => assoc_entryRG_tac ctxt i
 THEN REPEAT_ALL_NEW (assoc_app_tac ctxt) i THEN TRYALL (rt ctxt (@{thm small_step_eqv_refl})))


val _ =
  Theory.setup
    (Method.setup @{binding assocR_tac} (Attrib.thms >> (fn _ => fn ctxt => 
      SIMPLE_METHOD' (fn i => CHANGED_PROP((TRY (assocLHS_tac ctxt i)) THEN 
                                           (TRY (assocRHS_tac ctxt i)) THEN
                                           (TRY (assocRG_tac ctxt i))))))
      "Associating sequential compositions to the right")

\<close>


lemma
" \<Turnstile> a \<sqsupseteq>\<^bsub>r\<^esub> a \<Longrightarrow> \<Turnstile> b \<sqsupseteq>\<^bsub>r\<^esub> b \<Longrightarrow> \<Turnstile> c \<sqsupseteq>\<^bsub>r\<^esub> c \<Longrightarrow>
  \<Turnstile> d \<sqsupseteq>\<^bsub>r\<^esub> d \<Longrightarrow> \<Turnstile> e \<sqsupseteq>\<^bsub>r\<^esub> e \<Longrightarrow> \<Turnstile> f \<sqsupseteq>\<^bsub>r\<^esub> f \<Longrightarrow>
  \<Turnstile> ((a;b);c);((d;e);f) \<sqsupseteq>\<^bsub>r\<^esub> ((a;b);(c;d);e);f"
  (* apply plain_prog_corr_tac doesn't work, but *)
  apply assocR_tac
  by plain_prog_corr_tac

lemma
" \<Turnstile> {R, P} (a;b;c;d;e;f) {Q, G} \<Longrightarrow>
  \<Turnstile> {R, P} (((a;b);c);(d;(e;f))) {Q, G}"
  apply assocR_tac
  by assumption


end