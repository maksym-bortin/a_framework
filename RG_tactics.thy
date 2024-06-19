(* *********************************************************************

    Theory RG_tactics.thy is part of a framework for modelling,
    verification and transformation of concurrent imperative
    programs. Copyright (c) 2021  M. Bortin

    The framework is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.
    For more details see the license agreement (LICENSE) you should have
    received along with the framework.
    
   ******************************************************************* *)

theory RG_tactics
  imports Rules AssocR_tactic
begin

definition RG_deriv_VCG :: "(nat \<Rightarrow> 's LA) \<Rightarrow> bool \<Rightarrow> 's staterel \<Rightarrow> 's set \<Rightarrow> 's LA \<Rightarrow>
                              's set \<Rightarrow> 's staterel \<Rightarrow> bool"
("_ \<turnstile> _ {_ , _} _ {_ , _}" [40, 20, 20, 71, 20, 20] 71) 
where "(\<rho> \<turnstile> w {R, P} p {Q, G}) = (\<rho> \<Turnstile> {R, P} p {Q, G})"

lemma VCG_entry :
"\<rho> \<turnstile> False {R, P} p {Q, G} \<Longrightarrow> \<rho> \<Turnstile> {R, P} p {Q, G}"
  by(simp add: RG_deriv_VCG_def)

lemma VCG_exit :
"\<rho> \<Turnstile> {R, P} p {Q, G} \<Longrightarrow> \<rho> \<turnstile> w {R, P} p {Q, G}"
  by(simp add: RG_deriv_VCG_def)

lemma SkipT_VCG   : 
"\<rho> \<turnstile> True {R, P} Skip {P, G}"
  by(simp add: RG_deriv_VCG_def, rule SkipRule)

lemma SkipF_VCG   : 
"P \<subseteq> Q \<Longrightarrow> \<rho> \<turnstile> False {R, P} Skip {Q, G}"
  by(simp add: RG_deriv_VCG_def, rule ConseqRG, rule SkipRule, (rule subset_refl)+, assumption, 
     rule subset_refl)


lemma Basic_VCG  : 
 "P \<subseteq> {s. f s \<in> Q \<and> (s, f s) \<in> G} \<Longrightarrow> 
  R `` P \<subseteq> P \<Longrightarrow>
  \<rho> \<turnstile> w {R, P} (Basic f) {Q, G}"
  by(simp add: RG_deriv_VCG_def, erule BasicRule, assumption+)

lemma BasicF_VCG  : 
 "P \<subseteq> {s. f s \<in> Q \<and> (s, f s) \<in> G} \<Longrightarrow> 
  R `` P \<subseteq> P \<Longrightarrow>
  \<rho> \<turnstile> False {R, P} (Basic f) {Q, G}"
  by(erule Basic_VCG)

lemma BasicT_VCG  : 
 "R `` {s. f s \<in> Q \<and> (s, f s) \<in> G} \<subseteq> {s. f s \<in> Q \<and> (s, f s) \<in> G} \<Longrightarrow>
  \<rho> \<turnstile> True {R, {s. f s \<in> Q \<and> (s, f s) \<in> G}} (Basic f) {Q, G}"
  by(rule Basic_VCG, rule subset_refl, assumption)


lemma CondF_VCG   : 
 "\<rho> \<turnstile> False {R, (P \<inter> C)} p {Q, G} \<Longrightarrow>
  \<rho> \<turnstile> False {R, (P \<inter> -C)} q {Q, G} \<Longrightarrow>
  R `` P \<subseteq> P \<Longrightarrow>
  refl G \<Longrightarrow>
  \<rho> \<turnstile> False {R, P} (Cond C p q) {Q, G}"
  apply(simp add: RG_deriv_VCG_def)
  apply(erule CondRule, assumption+)
  done



lemma CondT_VCG : 
 "\<rho> \<turnstile> True {R, C1} p {Q, G} \<Longrightarrow>
  \<rho> \<turnstile> True {R, C2} q {Q, G} \<Longrightarrow>
  R `` {s. (s\<in>C \<longrightarrow> s\<in>C1) \<and> (s\<notin>C \<longrightarrow> s\<in>C2)} \<subseteq> {s. (s\<in>C \<longrightarrow> s\<in>C1) \<and> (s\<notin>C \<longrightarrow> s\<in>C2)} \<Longrightarrow>
  refl G \<Longrightarrow>
  \<rho> \<turnstile> True {R, {s. (s\<in>C \<longrightarrow> s\<in>C1) \<and> (s\<notin>C \<longrightarrow> s\<in>C2)}} (Cond C p q) {Q, G}" 
  apply(simp add: RG_deriv_VCG_def)
  apply(rule CondRule)
     apply(erule ConseqRG, rule subset_refl)
       apply fast
      apply(rule subset_refl)+
    apply(erule ConseqRG, rule subset_refl)
      apply fast
     apply(rule subset_refl)+
  by assumption+



lemma WhileT_VCG   : 
 "\<rho> \<turnstile> False {R, (I \<inter> C)} p {I, G} \<Longrightarrow> 
  \<rho> \<turnstile> False {R, (I \<inter> -C)} q {Q, G} \<Longrightarrow> 
  R `` I \<subseteq> I \<Longrightarrow>
  refl G \<Longrightarrow>
  \<rho> \<turnstile> True {R, I} (While C I p q) {Q, G}" 
  apply(simp add: RG_deriv_VCG_def)
  apply(rule ConseqRG[rotated 1])
      apply(rule subset_refl)
     apply(rule subset_refl)+
  apply(rule WhileRule, assumption+)
  done



lemma WhileF_VCG   : 
 "\<rho> \<turnstile> False {R, (I \<inter> C)} p {I, G} \<Longrightarrow> 
  \<rho> \<turnstile> False {R, (I \<inter> -C)} q {Q, G} \<Longrightarrow> 
  R `` I \<subseteq> I \<Longrightarrow>
  refl G \<Longrightarrow>
  P \<subseteq> I \<Longrightarrow>
  \<rho> \<turnstile> False {R, P} (While C I p q) {Q, G}" 
  apply(simp add: RG_deriv_VCG_def)
  apply(rule ConseqRG[rotated 1])
      apply(rule subset_refl)
     apply assumption
    apply(rule subset_refl)+
  apply(rule WhileRule, assumption+)
  done




lemma AwaitF1_VCG : 
 "(\<And>await_aux. \<rho> \<turnstile> False {{}, (P \<inter> C \<inter> {await_aux})} p 
                   {{t. (await_aux, t) \<in> G \<and> t \<in> Q}, 
                    UNIV}) \<Longrightarrow>
  R `` P \<subseteq> P \<Longrightarrow>
  \<rho> \<turnstile> False {R, P} (Await C UNIV p) {Q, G}"
  by(simp add: RG_deriv_VCG_def, erule AwaitRule)

lemma AwaitF2_VCG : 
 "(\<And>await_aux. \<rho> \<turnstile> False {{}, (a \<inter> {await_aux})} p 
                   {{t. (await_aux, t) \<in> G \<and> t \<in> Q}, 
                    UNIV}) \<Longrightarrow>
  R `` P \<subseteq> P \<Longrightarrow>
  P \<inter> C \<subseteq> a \<Longrightarrow>
  \<rho> \<turnstile> False {R, P} (Await C a p) {Q, G}"
  apply(simp add: RG_deriv_VCG_def, rule AwaitRule)
   apply(drule_tac x=await_aux in meta_spec)
   apply(erule ConseqRG, rule subset_refl, fast+)
  done


lemma AwaitT1_VCG : 
"(\<And>await_aux. \<rho> \<turnstile> True {{}, P' await_aux} p 
                   {{t. (await_aux, t) \<in> G \<and> t \<in> Q}, 
                    UNIV}) \<Longrightarrow>
  P \<subseteq> {s. s \<in> C \<longrightarrow> s \<in> P' s} \<Longrightarrow>
  R `` P \<subseteq> P \<Longrightarrow>
  \<rho> \<turnstile> True {R, P} (Await C UNIV p) {Q, G}" 
  apply(simp add: RG_deriv_VCG_def, rule AwaitRule)
    apply(drule_tac x=await_aux in meta_spec)+
    apply(erule ConseqRG, rule subset_refl, fast, (rule subset_refl)+)
   apply assumption+
  done

lemma AwaitT2_VCG : 
"(\<And>await_aux. \<rho> \<turnstile> False {{}, (a \<inter> C \<inter> {await_aux})} p 
                   {{t. (await_aux, t) \<in> G \<and> t \<in> Q}, 
                    UNIV}) \<Longrightarrow>
  R `` a \<subseteq> a \<Longrightarrow>
  \<rho> \<turnstile> True {R, a} (Await C a p) {Q, G}" 
  apply(simp add: RG_deriv_VCG_def, rule AwaitRule)
    apply(drule_tac x=await_aux in meta_spec)+
    apply(erule ConseqRG, rule subset_refl, fast, (rule subset_refl)+)
   apply assumption+
  done




lemma SeqT_VCG    : 
 "\<rho> \<turnstile> True {R, V} p\<^sub>2 {Q, G} \<Longrightarrow> 
  \<rho> \<turnstile> True {R, P} p\<^sub>1 {V, G} \<Longrightarrow> 
  refl G \<Longrightarrow>
  (p\<^sub>2 = Skip \<Longrightarrow> R `` Q \<subseteq> Q) \<Longrightarrow> 
  \<rho> \<turnstile> True {R, P} (Seq p\<^sub>1 p\<^sub>2) {Q, G}"
  by(simp add: RG_deriv_VCG_def, erule SeqRule)

lemma SeqF_VCG    : 
 "\<rho> \<turnstile> True {R, V} p\<^sub>2 {Q, G} \<Longrightarrow> 
  \<rho> \<turnstile> False {R, P} p\<^sub>1 {V, G} \<Longrightarrow> 
  refl G \<Longrightarrow>
  (p\<^sub>2 = Skip \<Longrightarrow> R `` Q \<subseteq> Q) \<Longrightarrow> 
  \<rho> \<turnstile> False {R, P} (Seq p\<^sub>1 p\<^sub>2) {Q, G}"
  by(simp add: RG_deriv_VCG_def, erule SeqRule)


lemma Parallel_VCG : 
"(\<And>i. i < length ps \<Longrightarrow> 
      \<rho> \<turnstile> False {ap_rely(snd(ps!i)), ap_precond(snd(ps!i))} fst(ps!i) 
                {ap_postcond (snd(ps!i)), \<Inter>{ap_rely(snd(ps!j)) |j. j \<noteq> i \<and> j < length ps} \<inter> G }) \<Longrightarrow>
  refl G \<Longrightarrow>
  (\<And>i. i < length ps \<Longrightarrow> ap_rely(snd(ps!i)) `` ap_postcond(snd(ps!i)) \<subseteq> 
                         ap_postcond(snd(ps!i))) \<Longrightarrow>
   R \<subseteq> \<Inter>{ap_rely(snd(ps!i)) |i. i < length ps} \<Longrightarrow>
   (P \<subseteq> \<Inter>{ap_precond(snd(ps!i)) |i. i < length ps}) \<Longrightarrow>
   (\<Inter>{ap_postcond (snd(ps!i)) |i. i < length ps} \<subseteq> Q) \<Longrightarrow>
   \<rho> \<turnstile> w {R, P} (Parallel ps) {Q, G}"
  apply(simp add: RG_deriv_VCG_def)
  apply(rule ConseqRG)
  by(erule ParallelRule, clarsimp+)

    

lemma cases_inter :
"\<forall>x. ((\<exists>i. x = F i \<and> i < Suc N) \<longrightarrow> a \<in> x) \<Longrightarrow>
 (\<forall>x. ((\<exists>i. x = F i \<and> i < N) \<longrightarrow> a \<in> x)) \<and> a \<in> F N"
  apply(frule spec, drule mp, rule_tac x="N" in exI, rule conjI, rule refl, simp (no_asm))
  apply(rule conjI)
   apply clarsimp
   apply(drule spec, drule mp, rule_tac x="i" in exI, rule conjI, rule refl, simp (no_asm))
  by assumption


ML \<open>


fun inst_check (Const ("HOL.Trueprop", _) $
     (Const ("Orderings.ord_class.less_eq", _) $
       l $ Var r)) = (l = Var r)
  | inst_check _ = true

fun subset_tac ctxt =
    SUBGOAL (fn (goal, i) =>
       if inst_check (Logic.strip_assums_concl goal)
       then resolve_tac ctxt [@{thm subset_refl}] i 
       else no_tac)


fun rts ctxt t i =
  resolve_tac ctxt t i

fun rt ctxt t i =
  resolve_tac ctxt [t] i

fun et ctxt t i =
  eresolve_tac ctxt [t] i

fun dt ctxt t i =
  dresolve_tac ctxt [t] i


fun simp ctxt extra =
  simp_tac (put_simpset HOL_basic_ss ctxt addsimps extra)

fun simp_only ctxt simps =
  simp_tac ((clear_simpset ctxt) addsimps simps)


val enable_trace = false;
fun trace str = if enable_trace then tracing str else ();


fun subst_def ctxt def = EqSubst.eqsubst_tac ctxt [0] [def]



fun rg_aux_tac1 ctxt i = (subst_def ctxt (@{thm refl_on_def}) i) THEN (safe_asm_full_simp_tac ctxt i)
                        ORELSE
                        (safe_asm_full_simp_tac ctxt i)


fun rg_aux_tac2 ctxt i = subset_tac ctxt i 
                         ORELSE (rg_aux_tac1 ctxt i)

fun rg_aux_tac3 ctxt i = TRY ((subst_def ctxt (@{thm refl_on_def}) i) THEN (safe_asm_full_simp_tac ctxt i))



fun HoareRuleTac props ctxt i =
FIRST[(rt ctxt (@{thm HoareTripleRG_i}) i),
      (rt ctxt (@{thm VCG_entry}) i),
      ((rt ctxt (@{thm Parallel_VCG})) THEN_ALL_NEW (rg_aux_tac1 ctxt)) i,
      ((rt ctxt (@{thm SeqT_VCG})) THEN_ALL_NEW (rg_aux_tac3 ctxt)) i,
      ((rt ctxt (@{thm SeqF_VCG})) THEN_ALL_NEW (rg_aux_tac3 ctxt)) i,
      (rt ctxt (@{thm SkipT_VCG})) i,
      ((rt ctxt (@{thm SkipF_VCG})) THEN_ALL_NEW (rg_aux_tac2 ctxt)) i,
      ((rt ctxt (@{thm BasicF_VCG})) THEN_ALL_NEW (rg_aux_tac2 ctxt)) i,
      ((rt ctxt (@{thm BasicT_VCG})) THEN_ALL_NEW (rg_aux_tac3 ctxt)) i,
      ((rt ctxt (@{thm CondT_VCG})) THEN_ALL_NEW (rg_aux_tac3 ctxt)) i,
      ((rt ctxt (@{thm CondF_VCG})) THEN_ALL_NEW (rg_aux_tac2 ctxt)) i,
      ((rt ctxt (@{thm WhileT_VCG})) THEN_ALL_NEW (rg_aux_tac1 ctxt)) i,
      ((rt ctxt (@{thm WhileF_VCG})) THEN_ALL_NEW (rg_aux_tac1 ctxt)) i,
      ((rt ctxt (@{thm AwaitF1_VCG})) THEN_ALL_NEW (rg_aux_tac2 ctxt)) i,
      ((rt ctxt (@{thm AwaitF2_VCG})) THEN_ALL_NEW (rg_aux_tac2 ctxt)) i,
      ((rt ctxt (@{thm AwaitT1_VCG})) THEN_ALL_NEW (rg_aux_tac3 ctxt)) i,
      ((rt ctxt (@{thm AwaitT2_VCG})) THEN_ALL_NEW (rg_aux_tac3 ctxt)) i,
      ((rt ctxt (@{thm VCG_exit}) i) THEN (rt ctxt (@{thm ConseqRG}) i) THEN 
       ((rts ctxt props) THEN_ALL_NEW (fn j => TRY (assume_tac ctxt j))) i),
      (et ctxt (@{thm PCasesE'}) i) THEN (safe_simp_tac ctxt i)]


fun rg_post_tac ctxt =
 TRYALL (subset_tac ctxt) THEN
 TRYALL (resolve_tac ctxt [@{thm subset_refl}]) THEN 
 TRYALL (clarsimp_tac ctxt) THEN
 TRYALL (REPEAT_ALL_NEW (fn i => rt ctxt (@{thm conjI}) i)) THEN
 TRYALL (clarsimp_tac ctxt) THEN
 TRYALL (fn i => ((rt ctxt (@{thm VCG_exit}) i))) THEN 
 TRYALL (REPEAT_ALL_NEW (fn i => (et ctxt (@{thm PCasesE}) i) THEN (clarsimp_tac ctxt i))) THEN
 TRYALL (REPEAT_ALL_NEW (fn i => (dt ctxt (@{thm cases_inter}) i) THEN (et ctxt (@{thm conjE}) i))) THEN
 TRYALL (clarsimp_tac ctxt)


\<close>



ML \<open>

fun mk_rg_ctxt ctxt = (ctxt delsimps [@{thm "Lattices.semilattice_inf_class.inf.bounded_iff"}])

fun rg_tac props ctxt =
 let val ctxt' = mk_rg_ctxt ctxt in
   SUBGOAL (fn (_, i) =>
   REPEAT_ALL_NEW (HoareRuleTac props ctxt') i THEN
   TRY (rg_post_tac ctxt'))
 end


val sc = Scan.optional(Scan.lift (Args.$$$ "use" -- Args.colon) |-- Attrib.thms) []

val _ =
  Theory.setup
    (Method.setup @{binding rg_tac}   (sc >> (fn ths => fn ctxt => 
      SIMPLE_METHOD' (rg_tac ths ctxt)))
      "verification condition generator for RG")
    


\<close>



end
