(* *********************************************************************

    Theory Rules.thy is part of a framework for modelling,
    verification and transformation of concurrent imperative
    programs. Copyright (c) 2021  M. Bortin

    The framework is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.
    For more details see the license agreement (LICENSE) you should have
    received along with the framework.
    
   ******************************************************************* *)

theory Rules
imports Rules_prelims ProgCorr
begin



lemma SkipRule :
"\<rho> \<Turnstile> {R, P} Skip {P, G}"
  apply(subst HoareTripleRG_def)
  apply clarify
  apply(rename_tac sq)
  apply simp
  apply(frule_tac Q=UNIV in Skip_pcs, simp, simp)
  apply clarsimp
  apply(rule conjI, simp add: TermCond_def)
   apply(rule conjI, erule exI)
   apply(clarsimp simp: InitCond_def)
   apply(rule_tac x=0 in exI, simp)
   apply(subst (asm) hd_conv_nth, erule pcs_noNil)
   apply(drule pcs0)
   apply fastforce
  apply(simp add: ProgCond_def)
  apply(rule conjI, erule exI)
  apply(clarsimp simp: cstep_cond_def)
  apply(drule sym)
  apply(drule_tac x="i-1" in spec, drule mp, simp)
  apply clarsimp
  apply(drule_tac i=i in pcs_nth, assumption+)
  apply(clarsimp, drule stepR_D1)
  apply(erule Skip_pstep)
  done
   

subsection "A rule for Basic"

lemma BasicRule :
"P \<subseteq> {x. f x \<in> Q \<and> (x, f x) \<in> G} \<Longrightarrow> 
 R `` P \<subseteq> P \<Longrightarrow>
 \<rho> \<Turnstile> {R, P} Basic f {Q, G}"
  apply(simp only: HoareTripleRG_def pcs_def)
  apply clarify
  apply(simp add: InitCond_def)
  apply clarify
  apply(frule COMP_noNil)
  apply(subst (asm) hd_conv_nth, assumption)
  apply(subgoal_tac "sq \<in> \<lbrakk>Basic f\<rbrakk>\<^sub>\<rho>")
   prefer 2
   apply(simp add: pcs_def)
   apply(subst hd_conv_nth, assumption)
   apply simp
  apply(case_tac "\<exists>j<length sq. 0 < j \<and> snd(sq!j)")
   apply(erule exE)
   apply(drule_tac j=j and P="\<lambda>x. x < length sq \<and> 0 < x \<and> snd (sq ! x)" in least_ix)
   apply clarsimp
   apply(subgoal_tac "\<forall>k<i. fst(fst(sq!k)) = Basic f \<and> snd(fst(sq!k)) \<in> P")
    apply(case_tac "sq!i", clarsimp)
    apply(rename_tac p' t tk')
    apply(case_tac "sq!(i-1)", clarsimp)
    apply(rename_tac p s tk)
    apply(frule_tac x="i-1" in spec, drule mp, simp, erule conjE)
    apply clarsimp
    apply(frule_tac i=i in COMP_nth, simp, assumption)
    apply clarsimp
    apply(drule stepR_D1)
    apply(drule Basic_pstep, clarsimp)
    apply(drule_tac c=s in subsetD, assumption)
    apply clarsimp
    apply(rule conjI)
     apply(simp add: TermCond_def)
     apply(rule conjI, erule exI)
     apply clarsimp
     apply(rename_tac j')
     apply(case_tac "j' < i")
      apply(drule_tac x=j' in spec, drule mp, assumption)+
      apply clarsimp
     apply(drule leI)
     apply(rule_tac x=i in exI, simp, rule_tac x=True in exI, simp (no_asm))
    apply(simp add: ProgCond_def)
    apply(rule conjI, erule exI)
    apply clarify
    apply(rename_tac i')
    apply(case_tac "sq!i'", clarsimp)
    apply(rename_tac c' s' tk')
    apply(case_tac "sq!(i' - 1)", clarsimp)
    apply(rename_tac c s tk)
    apply(clarsimp simp add: cstep_cond_def)
    apply(case_tac "i' < i")
     apply(drule_tac x=i' in spec, drule mp, assumption, clarsimp)
    apply(case_tac "i' = i", clarsimp)
    apply(subgoal_tac "c = Skip", clarify)
     apply(drule_tac i=i' in COMP_nth, simp, assumption)
     apply clarsimp
     apply(drule stepR_D1)
     apply(erule Skip_pstep)
    apply(subgoal_tac "drop i sq \<in> \<lbrakk>Skip\<rbrakk>\<^sub>\<rho>")
     apply(drule_tac sq="drop i sq" and Q=UNIV in Skip_pcs)
       apply(simp (no_asm))
      apply(simp (no_asm))
     apply(drule_tac x="i' - i - 1" in spec, drule mp, subst length_drop)
      apply simp
     apply clarsimp
    apply(drule_tac su="drop i sq" in pcs_suffix_cls)
      apply(rule suffix_drop)
     apply clarsimp
    apply clarsimp
   apply clarsimp
   apply(subgoal_tac "take i sq \<in> \<lbrakk>Basic f\<rbrakk>\<^sub>\<rho>")
    apply(drule_tac sq="take i sq" and P=P in esteps_pcs)
      apply clarify
      apply(rename_tac i')
      apply(rule conjI, fastforce)
      apply clarsimp
      apply(drule_tac x=i' in spec, drule mp, assumption)
      apply simp
      apply(case_tac "sq!(i' - 1)", clarsimp)
      apply(rename_tac u v w)
      apply(case_tac "sq!i'", clarsimp)
      apply(rename_tac u' v' w')
      apply(drule_tac i=i' in EnvCond_D,simp, assumption+)
      apply(drule_tac c=v' in subsetD, erule ImageI, simp)
      apply simp
     apply clarsimp
    apply clarsimp
   apply(erule_tac sq=sq in pcs_prefix_cls)
    apply(rule prefix_take, clarsimp)     
  apply(drule_tac p="Basic f" and P=UNIV in esteps_pcs)
    apply fastforce
   apply(simp (no_asm))
  apply clarsimp
  apply(rule conjI)
   apply(simp add: TermCond_def, erule exI)
  apply(simp add: ProgCond_def)
  apply(rule conjI, erule exI)
  apply(clarsimp simp add: cstep_cond_def)
  apply(drule_tac x=i in spec, drule mp, assumption)
  apply clarsimp
  done





subsection "A rule for Cond"

lemma CondRule :
"\<rho> \<Turnstile> {R, P \<inter> C} p {Q, G} \<Longrightarrow>
 \<rho> \<Turnstile> {R, P \<inter> -C} q {Q, G} \<Longrightarrow>
 R `` P \<subseteq> P \<Longrightarrow>
 refl G \<Longrightarrow>
 \<rho> \<Turnstile> {R, P} Cond C p q {Q, G}"
  apply(subst HoareTripleRG_def, clarify)
  apply(rename_tac sq)
  apply(clarsimp simp: pcs_def InitCond_def)
  apply(rename_tac s0 tk0)
  apply(frule COMP_noNil)
  apply(subst (asm) hd_conv_nth, assumption)
  apply(subgoal_tac "sq \<in> \<lbrakk>Cond C p q\<rbrakk>\<^sub>\<rho>")
   prefer 2
   apply(simp add: pcs_def)
   apply(subst hd_conv_nth, assumption)
   apply simp
  apply(case_tac "\<exists>j<length sq. 0 < j \<and> snd(sq!j)")
   apply(erule exE)
   apply(drule_tac j=j and P="\<lambda>x. x < length sq \<and> 0 < x \<and> snd (sq ! x)" in least_ix)
   apply clarsimp
   apply(subgoal_tac "\<forall>k<i. fst(fst(sq!k)) = Cond C p q \<and> snd(fst(sq!k)) \<in> P")
    apply(case_tac "sq!i", clarsimp)
    apply(rename_tac p'' t tk')
    apply(case_tac "sq!(i-1)", clarsimp)
    apply(rename_tac p' s tk)
    apply(frule_tac x="i - 1" in spec, drule mp, simp, erule conjE)
    apply clarsimp
    apply(frule_tac i=i in COMP_nth, simp, assumption)
    apply clarsimp
    apply(drule stepR_D1)
    apply(drule Cond_pstep, clarify)
    apply(erule disjE, clarsimp)
     apply(subst (asm) HoareTripleRG_def[where p=p])
     apply(drule_tac c="drop i sq" in subsetD)
      apply(simp, rule conjI)
       apply(erule EnvCond_suffix_cls, rule suffix_drop, simp, rule subset_refl)
      apply(subgoal_tac "drop i sq \<in> \<lbrakk>p\<rbrakk>\<^sub>\<rho>", simp add: InitCond_def)
       apply(rule conjI, erule exI)
       apply(subst hd_conv_nth, simp)
       apply(simp, rule_tac x=True in exI, simp)
      apply(drule_tac su="drop i sq" in pcs_suffix_cls, rule suffix_drop, simp)
      apply simp
     apply clarify
     apply(erule drop_conds, assumption+, fastforce, fastforce)
    apply clarify
    apply(subst (asm) HoareTripleRG_def[where p=q])
    apply(drule_tac c="drop i sq" in subsetD)
     apply(simp, rule conjI)
      apply(erule EnvCond_suffix_cls, rule suffix_drop, simp, rule subset_refl)
     apply(subgoal_tac "drop i sq \<in> \<lbrakk>q\<rbrakk>\<^sub>\<rho>", simp add: InitCond_def)
      apply(rule conjI, erule exI)
      apply(subst hd_conv_nth, simp)
      apply(simp, rule_tac x=True in exI, simp)
     apply(drule_tac su="drop i sq" in pcs_suffix_cls, rule suffix_drop, simp)
     apply simp
    apply clarify
    apply(erule drop_conds, assumption+, fastforce, fastforce)
   apply(subgoal_tac "take i sq \<in> \<lbrakk>Cond C p q\<rbrakk>\<^sub>\<rho>")
    apply(drule_tac sq="take i sq" and P=P in esteps_pcs)
      apply clarify
      apply(rename_tac i')
      apply(rule conjI, fastforce)
      apply clarsimp
      apply(drule_tac x=i' in spec, drule mp, assumption)
      apply clarsimp
      apply(case_tac "sq!(i' - 1)", clarsimp)
      apply(rename_tac u v w)
      apply(case_tac "sq!i'", clarsimp)
      apply(rename_tac u' v' w')
      apply(drule_tac i=i' in EnvCond_D,simp, assumption+)
      apply(drule_tac c=v' in subsetD, erule ImageI, simp)
      apply simp
     apply clarsimp
    apply clarsimp
   apply(erule_tac sq=sq in pcs_prefix_cls)
    apply(rule prefix_take, clarsimp)     
  apply(frule_tac p="Cond C p q" and P=UNIV in esteps_pcs)
    apply force
   apply(simp (no_asm))
  apply clarsimp
  apply(rule conjI)
   apply(simp add: TermCond_def, erule exI)
  apply(simp add: ProgCond_def)
  apply(rule conjI, erule exI)
  apply(clarsimp simp add: cstep_cond_def)
  apply(drule_tac x=i in spec, drule mp, assumption)
  apply clarsimp
  done


corollary CJumpRule :
"\<rho> \<Turnstile> {R, P \<inter> C} \<rho> i {Q, G} \<Longrightarrow> 
 \<rho> \<Turnstile> {R, P \<inter> -C} p {Q, G} \<Longrightarrow> 
 R `` P \<subseteq> P \<Longrightarrow>
 refl G \<Longrightarrow>
 \<rho> \<Turnstile> {R, P} CJump C i p {Q, G}"
  apply(subgoal_tac "\<rho> \<Turnstile> {R, P} CJump (-(-C)) i p {Q, G}", simp)
  apply(subst prog_corr_RG_eq[where \<rho>'=\<rho>])
   apply(rule small_step_eqv_sym)
   apply(rule eqv_condN, rule refl)
  apply(erule CondRule, simp_all)
  done


corollary JumpRule :
"\<rho> \<Turnstile> {R, P} \<rho> n {Q, G} \<Longrightarrow> 
 R `` P \<subseteq> P \<Longrightarrow>
 refl G \<Longrightarrow>
 \<rho> \<Turnstile> {R, P} Jump n {Q, G}"
  apply(simp add: Jump_def)
  apply(rule CJumpRule, simp_all)
  apply(rule ConseqRG)
  apply(rule SkipRule, (rule subset_refl)+, clarify, rule subset_refl)
  done



subsection "A rule for Await"


lemma AwaitRule[rule_format] :
"\<forall>await_aux. \<rho> \<Turnstile> {{}, P \<inter> C \<inter> {await_aux}} p 
                  {{t. (await_aux, t) \<in> G \<and> t \<in> Q},
                   UNIV} \<Longrightarrow> 
 R `` P \<subseteq> P \<Longrightarrow>
 \<rho> \<Turnstile> {R, P} Await C a p {Q, G}"
  apply(subst HoareTripleRG_def, clarify)
  apply(rename_tac sq)
  apply(clarsimp simp: pcs_def InitCond_def)
  apply(rename_tac s0 tk0)
  apply(frule COMP_noNil)
  apply(subst (asm) hd_conv_nth, assumption)
  apply(subgoal_tac "sq \<in> \<lbrakk>Await C a p\<rbrakk>\<^sub>\<rho>")
   prefer 2
   apply(simp add: pcs_def)
   apply(subst hd_conv_nth, assumption)
   apply simp
  apply(case_tac "\<exists>j<length sq. 0 < j \<and> snd(sq!j)")
   apply(erule exE)
   apply(drule_tac j=j and P="\<lambda>x. x < length sq \<and> 0 < x \<and> snd (sq ! x)" in least_ix)
   apply clarsimp
   apply(subgoal_tac "\<forall>k<i. fst(fst(sq!k)) = Await C a p \<and> snd(fst(sq!k)) \<in> P")
    apply(case_tac "sq!i", clarsimp)
    apply(rename_tac p'' t tk')
    apply(case_tac "sq!(i-1)", clarsimp)
    apply(rename_tac p' s tk)
    apply(frule_tac x="i - 1" in spec, drule mp, simp, erule conjE)
    apply clarsimp
    apply(frule_tac i=i in COMP_nth, simp, assumption)
    apply clarsimp
    apply(drule stepR_D1)
    apply(drule Await_pstep, clarsimp)
    apply(subst (asm) rtranclp_power)
    apply clarify
    apply(drule pstep_pow_COMP)
    apply clarify
    apply(rename_tac sqp)
    apply(drule_tac x=s in spec)
    apply(subgoal_tac "sqp \<in> \<lbrakk>p\<rbrakk>\<^sub>\<rho>")
     apply(subst (asm) HoareTripleRG_def)
     apply(drule_tac c=sqp in subsetD, simp)
      apply(rule conjI)
       apply(subst EnvCond_def, simp)
       apply(rule conjI, erule exI)
       apply(rule allI, rename_tac k)
       apply(clarsimp simp: cstep_cond_def)
       apply(drule_tac x=k in spec, drule mp, assumption)
       apply simp
      apply(subst InitCond_def, simp)
      apply(rule conjI, erule exI)
      apply(subst hd_conv_nth, erule pcs_noNil)
      apply(case_tac "sqp!0", clarsimp)
     apply clarify
     apply(drule TermCond_D)
     apply(drule_tac x=n in spec, drule mp, simp, drule mp, simp)
     apply clarsimp
     apply(rename_tac m t' tkt)
     apply(case_tac "m<n")
      apply(case_tac "sqp!(m+1)", clarsimp)
      apply(drule_tac x="Suc m" in spec, drule_tac P="Suc m < Suc n" in mp, simp)
      apply simp
      apply(drule_tac i="Suc m" and sq=sqp in pcs_nth, simp, simp)
      apply clarsimp
      apply(drule stepR_D1)
      apply(erule Skip_pstep)
     apply(drule leI, simp)
     apply(rule conjI)
      apply(subst TermCond_def, simp)
      apply(rule conjI, erule exI)
      apply(clarify, rename_tac k)
      apply(case_tac "k<i", fastforce)
      apply(rule_tac x=i in exI, simp)
      apply(rule_tac x=True in exI, simp (no_asm))
     apply(subst ProgCond_def, simp)
     apply(rule conjI, erule exI)
     apply(rule allI, rename_tac k)
     apply(clarsimp simp: cstep_cond_def)
     apply(case_tac "k<i", fastforce)
     apply(case_tac "k=i", simp)
     apply(drule_tac i=i and j="k-1" and Q=UNIV in Skip_COMP', 
            simp (no_asm), simp, simp (no_asm), assumption+, simp, simp)
     apply(drule_tac t="sq!(k-Suc 0)" in sym, clarsimp)
     apply(drule_tac i=k in pcs_nth, assumption, simp)
     apply clarsimp
     apply(drule stepR_D1)
     apply(erule Skip_pstep)
    apply(subst pcs_def, simp)
    apply(subst hd_conv_nth, erule COMP_noNil)
    apply(case_tac "sqp!0", simp)
   apply(subgoal_tac "take i sq \<in> \<lbrakk>Await C a p\<rbrakk>\<^sub>\<rho>")
    apply(drule_tac sq="take i sq" and P=P in esteps_pcs)
      apply clarify
      apply(rename_tac i')
      apply(rule conjI, fastforce)
      apply clarsimp
      apply(drule_tac x=i' in spec, drule mp, assumption)
      apply clarsimp
      apply(case_tac "sq!(i' - 1)", clarsimp)
      apply(rename_tac u v w)
      apply(case_tac "sq!i'", clarsimp)
      apply(rename_tac u' v' w')
      apply(drule_tac i=i' in EnvCond_D,simp, assumption+)
      apply(drule_tac c=v' in subsetD, erule ImageI, simp)
      apply simp
     apply clarsimp
    apply clarsimp
   apply(erule_tac sq=sq in pcs_prefix_cls)
    apply(rule prefix_take, clarsimp) 
  apply(frule_tac p="Await C a p" and P=UNIV in esteps_pcs)
    apply force
   apply(simp (no_asm))
  apply clarsimp
  apply(rule conjI)
   apply(simp add: TermCond_def, erule exI)
  apply(simp add: ProgCond_def)
  apply(rule conjI, erule exI)
  apply(clarsimp simp add: cstep_cond_def)
  apply(drule_tac x=i in spec, drule mp, assumption)
  apply clarsimp
  done


subsection "A rule for While"

lemma WhileRule :
"\<rho> \<Turnstile> {R, P \<inter> C} p {P, G} \<Longrightarrow>
 \<rho> \<Turnstile> {R, P \<inter> -C} q {Q, G} \<Longrightarrow>
 R `` P \<subseteq> P \<Longrightarrow>
 refl G \<Longrightarrow>
 \<rho> \<Turnstile> {R, P} While C I p q {Q, G}"
  apply(subst HoareTripleRG_def)
  apply(subst subset_iff)
  apply(rule allI)
  apply(rename_tac sq)
  apply(induct_tac sq rule: length_induct)
  apply clarsimp
  apply(rename_tac sq)
  apply(subgoal_tac "sq \<in> COMP \<rho>")
   prefer 2
   apply(simp add: pcs_def)
  apply(frule COMP_noNil)
  apply(case_tac "\<exists>j<length sq. 0 < j \<and> snd(sq!j)")
   prefer 2
   apply simp
   apply(frule_tac P=UNIV in esteps_pcs, fastforce, simp)
   apply(rule conjI, subst TermCond_def, simp)
    apply(erule exI)
   apply(subst ProgCond_def, simp)
   apply(rule conjI, erule exI)
   apply(clarsimp simp: cstep_cond_def)
   apply(drule_tac x=i in spec, drule mp, assumption)+
   apply simp
  apply(erule exE)
  apply(drule_tac j=j and P="\<lambda>x. x < length sq \<and> 0 < x \<and> snd (sq ! x)" in least_ix)
  apply clarsimp
  apply(subgoal_tac "\<forall>k<i. fst(fst(sq!k)) = While C I p q \<and> snd(fst(sq!k)) \<in> P")
   prefer 2
   apply(subgoal_tac "take i sq \<in> \<lbrakk>While C I p q\<rbrakk>\<^sub>\<rho>")
    apply(drule_tac sq="take i sq" and P=P in esteps_pcs)
      apply(rule allI, rename_tac k)
      apply clarsimp
      apply(rule conjI, fast)
      apply clarify
      apply(case_tac "sq!(k-1)", clarsimp)
      apply(rename_tac p' s' tk')
      apply(case_tac "sq!k", clarsimp)
      apply(rename_tac p'' s'' tk'')
      apply(drule_tac x=k in spec, drule mp, assumption)
      apply simp
      apply(erule subsetD)
      apply(rule_tac a=s' in ImageI)
       apply(erule_tac i=k in EnvCond_D, simp, assumption+)
     apply(clarsimp simp: InitCond_def)
     apply(subst (asm) hd_conv_nth, simp)+
     apply clarsimp
    apply clarsimp
   apply(erule pcs_prefix_cls, subst prefix_take, clarsimp, clarsimp)
  apply(case_tac "sq!i", clarsimp)
  apply(rename_tac p'' t tk')
  apply(case_tac "sq!(i-1)", clarsimp)
  apply(rename_tac p' s tk)
  apply(frule_tac x="i - 1" in spec, drule mp, simp, erule conjE)
  apply clarsimp
  apply(frule_tac i=i in COMP_nth, simp, assumption)
  apply clarsimp
  apply(drule stepR_D1)
  apply(drule While_pstep, clarify)
  apply(erule disjE, clarsimp)
   prefer 2
   apply clarsimp
   apply(subst (asm) HoareTripleRG_def[where p="q"])
   apply(drule_tac c="drop i sq" in subsetD, simp)
    apply(rule conjI)
     apply(erule EnvCond_suffix_cls, rule suffix_drop, simp, rule subset_refl)
    apply(subgoal_tac "drop i sq \<in> \<lbrakk>q\<rbrakk>\<^sub>\<rho>", simp add: InitCond_def)
     apply(rule conjI, erule exI)
     apply(subst hd_conv_nth, simp)
     apply(simp, rule_tac x=True in exI, simp)
    apply(simp add: pcs_def)
    apply(rule conjI, erule COMP_suffix_cls, rule suffix_drop, simp)
    apply(subst hd_conv_nth, simp)
    apply(simp, rule_tac x=True in exI, simp)
   apply clarify
   apply(erule drop_conds, assumption+, fastforce)
   apply fastforce
  apply(thin_tac "\<rho> \<Turnstile> {R, P \<inter> -C} q {Q, G} ")
  apply(subgoal_tac "drop i sq \<in> \<lbrakk>(p;Skip;While C I p q)\<rbrakk>\<^sub>\<rho>")
   prefer 2
   apply(subst pcs_def, simp)
   apply(rule conjI, erule COMP_suffix_cls, rule suffix_drop, simp)
   apply(subst hd_conv_nth, simp)
   apply(simp, rule_tac x=True in exI, simp (no_asm))
  apply(case_tac "\<exists>k<length(drop i sq). 0 < k \<and> snd((drop i sq)!k) \<and> 
                  progOf((drop i sq)!(k-1)) = Skip;Skip;While C I p q")
   prefer 2
   apply simp
   apply(drule_tac sq="drop i sq" in Seq_split)
    apply clarsimp
    apply(rename_tac k)
    apply(drule_tac x=k in spec, drule mp, assumption)
    apply simp
   apply clarsimp
   apply(rule conjI, subst TermCond_def, simp)
    apply(rule conjI,  erule exI)
    apply clarsimp
    apply(rename_tac k)
    apply(case_tac "k < i", fastforce)
    apply(drule leI)
    apply(drule_tac x="k - i" in spec, drule_tac P="k-i<length sq - i" in mp, simp)
    apply clarsimp
   apply(subst (asm) HoareTripleRG_def)
   apply(drule_tac c=sq1 in subsetD, simp)
    apply(rule conjI)
    apply(subst EnvCond_def, simp)
    apply(rule conjI, erule exI)
     apply(rule allI, rename_tac l)
     apply(clarsimp simp: cstep_cond_def)
     apply(frule_tac x=l in spec, drule mp, assumption)
     apply(drule_tac x="l-1" in spec, drule_tac P="l-1 < length sq - i" in mp, simp)
     apply(drule_tac t="sq1 ! (l - Suc 0)" in sym)
     apply clarsimp
     apply(erule_tac i="i+l" in EnvCond_D, simp,simp, assumption+)
    apply(subst InitCond_def, simp)
    apply(rule conjI, erule exI)
    apply(subst hd_conv_nth, simp, erule pcs_noNil)
    apply(drule_tac x=0 in spec, drule_tac P="0<length sq - i" in mp, simp)
    apply(case_tac "sq1!0", clarsimp)
    apply(rule_tac x=True in exI, simp (no_asm))
   apply clarify
   apply(subst ProgCond_def, simp)
   apply(rule conjI, erule exI)
   apply(rule allI, rename_tac k)
   apply(clarsimp simp: cstep_cond_def)
   apply(case_tac "k < i")
    apply(drule_tac x=k in spec, drule mp, assumption)
    apply simp
   apply(drule leI)
   apply(case_tac "k = i", clarsimp simp: refl_on_def)
   apply(frule_tac x="k-i" in spec, drule_tac P="k-i<length sq - i" in mp, simp)
   apply(drule_tac x="k-1-i" in spec, drule_tac P="k-1-i<length sq - i" in mp, simp)
   apply clarsimp
   apply(case_tac "sq1!(k-(i+1))", case_tac "sq1!(k-i)", clarsimp)
   apply(erule_tac i="k-i" in ProgCond_D, simp, simp, simp, assumption)
  apply(erule exE)
  apply(drule_tac j=k and P="\<lambda>x. (x<length(drop i sq) \<and> 0 < x \<and> snd((drop i sq)!x) \<and> 
             progOf((drop i sq)!(x-1)) = Skip;Skip;While C I p q)" in least_ix)
  apply clarsimp
  apply(rename_tac i1)
  apply(subgoal_tac "take i1 (drop i sq) \<in> \<lbrakk>(p;Skip;While C I p q)\<rbrakk>\<^sub>\<rho>")
   prefer 2  
   apply(erule pcs_prefix_cls, rule prefix_take, clarsimp)
  apply(drule_tac sq="take i1 (drop i sq)" in Seq_split)
   apply clarsimp
   apply(rename_tac l)
   apply(drule_tac x=l in spec, drule mp, assumption, drule mp, assumption)
   apply clarsimp
  apply(clarsimp simp: min_def)
  apply(subst (asm) HoareTripleRG_def)
  apply(subgoal_tac "sq1 \<in> EnvCond \<rho> R")
   apply(drule_tac c=sq1 in subsetD, simp)
    apply(subst InitCond_def, simp)
    apply(rule conjI, erule exI)
    apply(subst hd_conv_nth, simp)
    apply(drule_tac x=0 in spec, drule_tac P="0<length sq1" in mp, simp)+
    apply(case_tac "sq1!0", clarsimp)
    apply(rule_tac x=True in exI, simp (no_asm))
   prefer 2
   apply(subst EnvCond_def, simp)
   apply(rule conjI, erule exI)
   apply(rule allI, rename_tac l)
   apply(clarsimp simp: cstep_cond_def)
   apply(drule_tac x=l in spec, drule mp, assumption)
   apply(frule_tac x=l in spec, drule mp, assumption)
   apply(drule_tac x="l-1" in spec, drule_tac P="l-1<length sq1" in mp, simp)
   apply(drule_tac t="sq1 ! (l - Suc 0)" in sym, clarsimp)
   apply(erule_tac i="i+l" in EnvCond_D, simp,simp, assumption+)
  apply clarify
  apply(case_tac "sq ! (i + length sq1)", clarsimp)
  apply(rename_tac p1' s1' tk1')
  apply(case_tac "sq ! (i + length sq1 - 1)", clarsimp)
  apply(rename_tac p1 s1 tk1)
  apply(subgoal_tac "fst(sq1!(length sq1 - 1)) = (Skip, s1)")
   prefer 2
   apply(drule_tac x="length sq1 - 1" in spec, drule_tac P="length sq1 - 1 < length sq1" in mp, simp)+
   apply(subst (asm) add_diff_assoc, case_tac sq1, simp+)
   apply(case_tac "sq1!(length sq1 - 1)", clarsimp)
  apply(subgoal_tac "s1 \<in> P")
   prefer 2
   apply(thin_tac "\<forall>ys. length ys < length sq \<longrightarrow> _ ys")
   apply(thin_tac "\<forall>k<i. _ k")+
   apply(thin_tac "\<forall>i<length sq1. _ i")+
   apply(thin_tac "sq!_ = _")+
   apply(drule TermCond_D)
   apply(drule_tac x="length sq1 - 1" in spec, drule mp, simp, drule mp, simp)
   apply clarsimp
   apply(rename_tac k s0 tk0)
   apply(subgoal_tac "drop k sq1 \<in> \<lbrakk>Skip\<rbrakk>\<^sub>\<rho>")
    apply(drule_tac Q=P in Skip_pcs)
      apply(rule allI, rename_tac l)
      apply clarsimp
      apply(erule subsetD)
      apply(rule_tac a=s in ImageI)
       apply(erule_tac sq=sq1 and i="k+l" in EnvCond_D, simp, simp, assumption+)
     apply clarsimp
    apply simp
    apply(drule_tac x="length sq1 - k - 1" in spec, drule mp, case_tac sq1, simp+)
    apply(subst (asm) add_diff_assoc, case_tac sq1, simp+)+
   apply(case_tac "sq1!(length sq1 - 1)", clarsimp)
   apply(clarsimp simp: pcs_def)
   apply(rule conjI, erule COMP_suffix_cls, rule suffix_drop, clarsimp, case_tac sq1, clarsimp+)
   apply(subst hd_conv_nth, case_tac sq1, clarsimp+)
  apply(frule_tac sq=sq and i="i + length sq1" in pcs_nth, simp, simp)
  apply clarsimp
  apply(drule stepR_D1)
  apply(drule Seq_pstep_Skip, clarsimp)
  apply(case_tac "\<exists>j<length sq. i + length sq1 < j \<and> snd(sq!j)")
   prefer 2
   apply simp
   apply(rule conjI)
    apply(subst TermCond_def, simp)
    apply(rule conjI, erule exI)
    apply clarify
    apply(rename_tac k)
    apply(case_tac "k < i", drule_tac x=k in spec, drule mp, assumption, simp)
    apply(drule leI)
    apply(case_tac "k=i", clarsimp)
    apply(case_tac "i + length sq1 \<le> k")
     apply(subgoal_tac "drop (i + length sq1) sq \<in> \<lbrakk>(Skip;While C I p q)\<rbrakk>\<^sub>\<rho>")
      apply(drule_tac sq="drop (i + length sq1) sq" and P=UNIV in esteps_pcs, clarsimp, simp (no_asm))
      apply(drule_tac x="k - (i + length sq1)" in spec, 
            drule_tac P="k - (i + length sq1)<length (drop (i + length sq1) sq)" in mp, simp)
      apply simp
     apply(drule_tac sq=sq and su="drop (i + length sq1) sq" in pcs_suffix_cls)
       apply(rule suffix_drop, simp)
     apply simp
    apply(drule not_le_imp_less)
    apply(drule_tac x="k-i" in spec, drule_tac P="k-i<length sq1" in mp, simp)+
    apply clarsimp
   apply(subst ProgCond_def, simp)
   apply(rule conjI, erule exI)
   apply(rule allI, rename_tac k)
   apply(clarsimp simp: cstep_cond_def)
   apply(case_tac "k<i", drule_tac x=k in spec, drule mp, assumption, simp)
   apply(drule leI)
   apply(case_tac "k=i", clarsimp simp: refl_on_def)
   apply(case_tac "k>i+length sq1")
    apply(drule_tac x=k in spec, drule_tac P="k>i+length sq1" in mp, assumption)
    apply simp
   apply(drule leI)
   apply(case_tac "k=i+length sq1", clarsimp simp: refl_on_def)
   apply(drule_tac x="k-i" in spec, drule_tac P="k-i<length sq1" in mp, simp)
   apply(frule_tac x="k-i" in spec, drule_tac P="k-i<length sq1" in mp, simp)
   apply(drule_tac x="k-i-1" in spec, drule_tac P="k-i-1<length sq1" in mp, simp)
   apply(drule_tac t="sq ! (k - Suc 0)" in sym, clarsimp)
   apply(case_tac "sq1!(k - (i+1))", case_tac "sq1!(k - i)", clarsimp)
   apply(erule_tac i="k-i" in ProgCond_D, simp, simp, simp, assumption)
  apply(erule exE, rename_tac y)
  apply(drule_tac j=y and P="\<lambda>x. x < length sq \<and> i + length sq1 < x \<and> snd (sq ! x)" in least_ix)
  apply clarsimp
  apply(rename_tac i2)
  apply(case_tac "sq ! (i2-1)", clarsimp)
  apply(rename_tac p2 s2 tk2)
  apply(case_tac "sq ! i2", clarsimp)
  apply(rename_tac p2' s2' tk2')
  apply(subgoal_tac "p2 = Seq Skip (While C I p q) \<and> s2 \<in> P")
   prefer 2
   apply(thin_tac "\<forall>ys. length ys < length sq \<longrightarrow> _ ys")
   apply(thin_tac "\<forall>k<i. _ k")+
   apply(thin_tac "\<forall>i<length sq1. _ i")+
   apply(subgoal_tac "take (i2 - (i + length sq1)) (drop (i + length sq1) sq) \<in> COMP \<rho>")
    apply(drule_tac S=P and i="i2 - (i + length sq1) - 1" 
                and sq="take (i2 - (i + length sq1)) (drop (i + length sq1) sq)" in esteps_COMP)
       apply clarsimp
       apply(rename_tac l)
       apply(drule_tac x="i + length sq1 + l" in spec, drule mp, simp, drule mp, simp)
       apply(case_tac "sq!(i + length sq1 + l - Suc 0)", clarsimp)
       apply(rename_tac u v w)
       apply(case_tac "sq!(i + length sq1 + l)", clarsimp)
       apply(erule subsetD)
       apply(rule_tac a=v in ImageI)
        apply(erule_tac i="i + length sq1 + l" in EnvCond_D, simp, simp, assumption+)
      apply simp
     apply fastforce
    apply clarsimp
   apply(rule COMP_prefix_cls[rotated 1], rule prefix_take, simp)
   apply(erule COMP_suffix_cls, rule suffix_drop, simp)
  apply(frule_tac sq=sq and i=i2 in pcs_nth, simp, simp)
  apply clarsimp
  apply(drule stepR_D1)
  apply(drule Seq_pstep_Skip, clarsimp)
  apply(subgoal_tac "take (i2+1) sq \<in> ProgCond \<rho> G")
   prefer 2
   apply(thin_tac "\<forall>ys. length ys < length sq \<longrightarrow> _ ys")
   apply(thin_tac "\<forall>k<i. _ k \<and> _ k")
   apply(thin_tac "\<forall>k<length sq1. _ k \<longrightarrow> _ k")
   apply(subst ProgCond_def, simp)
   apply(rule conjI, rule exI, erule pcs_prefix_cls, rule prefix_take, simp)
   apply(rule allI, rename_tac l)
   apply(clarsimp simp: cstep_cond_def)
   apply(case_tac "l = i2", clarsimp simp: refl_on_def)
   apply(case_tac "i + length sq1 < l")
    apply(drule_tac x=l in spec, drule_tac P="l<i2" in mp, simp)
    apply clarsimp
   apply(drule leI)
   apply(case_tac "i + length sq1 = l", clarsimp simp: refl_on_def)
   apply(case_tac "i < l")
    apply(frule_tac x="l-i" in spec, drule_tac P="l-i<length sq1" in mp, simp)
    apply(drule_tac x="l-i-1" in spec, drule_tac P="l-i-1<length sq1" in mp, simp)
    apply(case_tac "sq1!(l - (i+1))", case_tac "sq1!(l - i)", clarsimp)
    apply(erule_tac sq=sq1 and i="l-i" in ProgCond_D, simp, simp, simp, assumption)
   apply(drule leI)
   apply(case_tac "l=i", clarsimp simp: refl_on_def)
   apply(drule_tac x=l in spec, drule_tac P="l<i" in mp, simp)
   apply clarsimp
  apply(drule_tac x="drop i2 sq" in spec, drule mp, simp)
  apply(drule mp, rule conjI, erule EnvCond_suffix_cls)
      apply(rule suffix_drop, simp)
    apply(rule subset_refl)
   apply(drule_tac sq=sq and su="drop i2 sq" in pcs_suffix_cls)
     apply(rule suffix_drop, simp)
   apply simp
   apply(simp (no_asm) add: InitCond_def)
   apply(rule conjI, erule exI)
   apply(subst hd_conv_nth, simp)
   apply simp
   apply(rule_tac x=True in exI, simp (no_asm))
  apply clarify
  apply(thin_tac "\<forall>k<length sq1. _ k \<longrightarrow> _ k")
  apply(rule conjI)
   apply(subst TermCond_def, simp)
   apply(rule conjI, erule exI)
   apply(rule allI, rename_tac k)
   apply clarify
   apply(case_tac "k < i", drule_tac x=k in spec, drule mp, assumption, simp)
   apply(drule leI)
   apply(case_tac "k=i", clarsimp)
   apply(case_tac "k < i + length sq1")
    apply(drule_tac x="k-i" in spec, drule_tac P="k-i<length sq1" in mp, simp+)
   apply(drule leI)
   apply(case_tac "i2 \<le> k")
    apply(drule_tac sq="drop i2 sq" in TermCond_D)
    apply(drule_tac x="k-i2" in spec, drule_tac P="k-i2<length (drop i2 sq)" in mp, simp)
    apply(drule mp, simp)
    apply(erule exE, rename_tac l)
    apply clarify
    apply(rule_tac x="i2+l" in exI, simp)
   apply(drule not_le_imp_less)
   apply(subgoal_tac "take (i2 - (i+length sq1)) (drop (i + length sq1) sq) \<in> \<lbrakk>Seq Skip (While C I p q)\<rbrakk>\<^sub>\<rho>")
    apply(drule_tac sq="take (i2 - (i+length sq1)) (drop (i + length sq1) sq)" and P=UNIV in esteps_pcs, clarsimp)
     apply(simp (no_asm))
    apply(drule_tac x="k - (i + length sq1)" in spec, 
            drule_tac P="k - (i + length sq1)<length (take (i2 - (i + length sq1)) (drop (i + length sq1) sq))" in mp, simp)
     apply fastforce
    apply clarsimp
  apply(drule_tac sq=sq and su="drop (i + length sq1) sq" in pcs_suffix_cls)
     apply(rule suffix_drop, simp)
   apply simp
   apply(erule pcs_prefix_cls, rule prefix_take, simp)
  apply(subst ProgCond_def, simp)
  apply(rule conjI, erule exI)
  apply(rule allI, rename_tac k)
  apply(clarsimp simp: cstep_cond_def)
  apply(case_tac "k \<le> i2")
   apply(erule_tac sq="take (Suc i2) sq" and i=k in ProgCond_D, simp, assumption, simp, erule sym)
   apply simp
  apply(drule not_le_imp_less)
  apply(erule_tac sq="drop i2 sq" and i="k-i2" in ProgCond_D, simp, simp, simp, erule sym)
  apply simp
  done



subsection "A rule for Parallel"


lemma ParallelRule[rule_format] :
"\<forall>i < length ps. \<rho> \<Turnstile> {R i, S i} 
                      fst(ps!i) 
                      {Q i, \<Inter>{R j |j. j \<noteq> i \<and> j < length ps} \<inter> G} \<Longrightarrow> 
 refl G \<Longrightarrow>
 \<forall>i < length ps. R i `` (Q i) \<subseteq> Q i \<Longrightarrow>
 \<rho> \<Turnstile> {\<Inter>{R i |i. i < length ps}, \<Inter>{S i |i. i < length ps}} 
      Parallel ps 
      {\<Inter>{Q i |i. i < length ps}, G}"
  apply(case_tac "length ps \<le> 0", simp add: HoareTripleRG_def)
   apply(rule conjI, clarify)
    apply(rename_tac sq)
    apply(simp add: TermCond_def)
    apply(rule conjI, erule exI)
    apply clarify
    apply(rule_tac x=j in exI)
    apply(case_tac "sq!j", clarsimp)
   apply clarify
   apply(rename_tac sq)
   apply(subst ProgCond_def, simp)
   apply(rule conjI, erule exI)
   apply(case_tac "\<exists>j<length sq. 0 < j \<and> snd(sq!j)")
    apply(erule exE)
    apply(drule_tac P="\<lambda>x. x<length sq \<and> 0<x \<and> snd(sq!x)" in least_ix)
    apply clarsimp
    apply(rename_tac k)
    apply(frule_tac pr="take i sq" in pcs_prefix_cls, rule prefix_take, simp, erule pcs_noNil)
    apply(drule_tac sq="take i sq" and P=UNIV in esteps_pcs,fastforce, simp (no_asm))
    apply(drule_tac x="i-1" in spec, drule mp, simp, erule conjE)
    apply(case_tac "sq!(i-1)")
    apply(case_tac "sq!i", clarsimp)
    apply(frule_tac i=i in pcs_nth, assumption+)
    apply clarsimp
    apply(drule stepR_D1)
    apply(drule Parallel_pstep_Skip, simp)
    apply clarify
    apply(clarsimp simp: cstep_cond_def)
    apply(case_tac "k < i", fastforce)
    apply(case_tac "k=i", clarsimp simp: refl_on_def)
    apply(frule pcsD)
    apply(drule_tac i=i and j="k-1" and Q=UNIV in Skip_COMP', simp (no_asm), simp, 
          simp (no_asm), assumption+, simp, simp)
    apply(drule_tac t="sq!(k-Suc 0)" in sym)
    apply clarsimp
    apply(drule_tac i=k in pcs_nth, assumption+, simp)
    apply clarsimp
    apply(drule stepR_D1)
    apply(erule Skip_pstep)
   apply(clarsimp simp: cstep_cond_def)
   apply(drule_tac x=i in spec, drule mp, simp)
   apply fastforce
  apply(drule not_le_imp_less)
  apply(simp (no_asm) only: HoareTripleRG_def)
  apply clarify
  apply(rename_tac sq)
  apply(frule pcs_noNil)
  apply(subgoal_tac "take (Parallel_ix sq) sq \<in> \<lbrakk>Parallel ps\<rbrakk>\<^sub>\<rho>")
   prefer 2
   apply(erule pcs_prefix_cls, rule prefix_take, erule Parallel_ix_take)
  apply(frule_tac sq="take (Parallel_ix sq) sq" in Parallel_split)
    apply simp
   apply clarsimp
   apply(drule Parallel_ix_least)
    apply assumption
   apply clarsimp
  apply clarsimp
  apply(drule_tac pr="take (Parallel_ix sq) sq" and A="\<Inter>{S i |i. i < length ps}" in InitCond_prefix_cls)
     apply(rule prefix_take, erule Parallel_ix_take, rule subset_refl)
  apply(frule_tac sqs=sqs and ps=ps in Parallel_simR_InitCond, simp, simp, erule Parallel_ix_gr, simp)
(* < EnvConds *) 
  apply(subgoal_tac "\<forall>n<length sqs. sqs!n \<in> EnvCond \<rho> (R n)")
   prefer 2
   apply(rule ccontr, clarsimp)
  apply(subgoal_tac "\<exists>\<mu> L. L < length ps \<and> 0 < \<mu> \<and> \<mu> < length(sqs!L) \<and> EnvCond_br \<rho> (R L) (sqs!L) \<mu> \<and>
        (\<forall>i L'. L' < length ps \<and> 0 < i \<and> i < length(sqs!L') \<and> EnvCond_br \<rho> (R L') (sqs!L') i \<longrightarrow> \<mu> \<le> i)")
    prefer 2
    apply(subgoal_tac "\<exists>F. F = (\<lambda>i. (\<exists>n<length sqs. 0 < i \<and> i < length(sqs!n) \<and> EnvCond_br \<rho> (R n) (sqs!n) i))")
     apply(erule exE)
     apply(subgoal_tac "F (Least F)")
      apply(rule_tac x="Least F" in exI)
      apply clarsimp
      apply(rename_tac L)
      apply(rule_tac x=L in exI, clarsimp)
      apply(rule Least_le)
      apply(rule_tac x=L' in exI, simp)
     apply(rule LeastI_ex, clarsimp)
     apply(drule spec, drule mp, assumption, clarsimp)
     apply(drule not_EnvCond_D, assumption)
     apply clarify
     apply(rule_tac x=i in exI)
     apply(rule_tac x=n in exI, clarsimp simp: EnvCond_br_def cstep_cond_def)
     apply(drule_tac t="sqs!n!(i - Suc 0)" in sym, clarsimp, fast)
    apply(rule exI, rule refl)
   apply clarify
   apply(subgoal_tac "\<exists>N<length ps. tkOf(sqs!N!\<mu>)")
    prefer 2
    apply(rule ccontr)
    apply(drule_tac x=L in spec, drule mp, assumption, erule conjE)
    apply(frule_tac x=\<mu> in spec, drule mp, rule conjI, simp, simp)
    apply(drule_tac x="\<mu>-1" in spec, drule mp, rule conjI, fastforce, fastforce)
    apply(clarsimp simp add: Parallel_simR_def)
    apply(rename_tac ps2 ps1 s2 s1)
    apply(case_tac "sq!(\<mu> - 1)")
    apply(case_tac "sq!\<mu>", clarsimp)
    apply(drule_tac i="\<mu>" in EnvCond_D)
        apply assumption+
     apply(erule_tac t="sq!\<mu>" in ssubst)
     apply clarsimp
     apply(rule conjI, rule refl)+
     apply clarify
     apply(drule mem_nth, fastforce)
    apply(clarsimp, drule_tac x="R L" in spec, drule mp, fast)
    apply(clarsimp simp: EnvCond_br_def)
    apply(drule_tac x="sqs!L" in bspec, rule nth_mem, simp)+
    apply simp
   apply clarify
   apply(subgoal_tac "take (\<mu> + 1) (sqs!N) \<in> EnvCond \<rho> (R N)")
    prefer 2
    apply(subst EnvCond_def, simp)
    apply(rule conjI)
     apply(rule_tac x="fst(ps!N)" in exI)
     apply(rule pcs_prefix_cls[rotated 1], rule prefix_take, clarsimp)
      apply(drule_tac x=N in spec, drule mp, assumption, erule conjE)
      apply simp
     apply(drule_tac x=N in spec, drule mp, assumption, erule conjE)
     apply simp
    apply(rule allI, rename_tac k)
    apply(clarsimp simp: cstep_cond_def)
    apply(case_tac "k=\<mu>", clarsimp)
    apply(rule ccontr)
    apply(drule_tac x=k in spec, drule mp, rule_tac x=N in exI, simp)
     apply(subst EnvCond_br_def, clarsimp)
     apply(drule_tac t="sqs!N!(k - Suc 0)" in sym, clarsimp)
    apply simp
   apply(subst (asm) HoareTripleRG_def)
   apply(drule_tac x=N in spec, drule mp, assumption)
   apply(drule_tac c="take (\<mu> + 1) (sqs!N)" in subsetD, simp)
    apply(drule_tac x=N in spec, drule mp, assumption)+
    apply clarify
    apply(rule conjI)
     apply(simp (no_asm) add: InitCond_def)
     apply(rule conjI, rule exI, rule pcs_prefix_cls[rotated 1], rule prefix_take)
       apply(simp, erule pcs_noNil)
      apply assumption
     apply(subst (asm) InitCond_def)+
     apply fastforce
    apply(rule pcs_prefix_cls[rotated 1], rule prefix_take)
     apply(simp, erule pcs_noNil)
    apply assumption
   apply clarify
   apply(case_tac "sqs!N!\<mu>")
   apply(case_tac "sqs!N!(\<mu> - 1)", clarsimp)
   apply(drule_tac i=\<mu> in ProgCond_D)
       apply simp
      apply assumption
     apply simp
    apply simp
   apply(clarsimp simp: EnvCond_br_def)
   apply(drule_tac x="R L" in spec, drule mp, rule_tac x=L in exI, simp, clarsimp)
   apply(frule_tac x=\<mu> in spec, drule mp, rule conjI)
     apply assumption+
   apply(drule_tac x="\<mu>-1" in spec, drule mp, rule conjI)
     apply simp
    apply simp
   apply(case_tac "sq!\<mu>")
   apply(case_tac "sq!(\<mu>-1)", clarsimp)
   apply(drule Parallel_simR_D)+
   apply clarsimp
   apply(frule_tac x="sqs!L" in bspec, rule nth_mem, simp)
   apply(drule_tac x="sqs!N" in bspec, rule nth_mem, simp)
   apply(frule_tac x="sqs!L" in bspec, rule nth_mem, simp)
   apply(drule_tac x="sqs!N" in bspec, rule nth_mem, simp)
   apply clarsimp
(* EnvConds > *) 
  apply(case_tac "\<exists>j<length sq. 0<j \<and> (sq!(j-1), sq!j) \<in> Parallel_break")
   apply clarsimp
   apply(drule Parallel_ix_break[simplified], assumption+)
   apply(clarsimp simp: min_def)
   apply(frule Parallel_ix_gr)
   apply(case_tac "sq!(Parallel_ix sq - 1)", clarsimp)
   apply(rename_tac p t tk)
   apply(case_tac "sq!(Parallel_ix sq)", clarsimp)
   apply(rename_tac p' t' tk')
   apply(frule_tac i="Parallel_ix sq" in pcs_nth, simp, assumption)
   apply clarsimp
   apply(frule Parallel_breakD)
   apply clarsimp
   apply(rename_tac ps')
   apply(drule stepR_D1)
   apply(frule Parallel_pstep_to_Skip, simp)
   apply(rule conjI, subst TermCond_def, simp)
    apply(rule conjI, erule exI)
    apply clarsimp
    apply(rename_tac k)
    apply(case_tac "k < Parallel_ix sq")
     apply(drule_tac x=k in spec, drule mp, rule conjI, assumption, assumption)
     apply(clarsimp simp: Parallel_simR_def)
    apply(drule leI)
    apply(rule_tac x="Parallel_ix sq" in exI)
    apply(rule conjI, assumption)
    apply simp
    apply(rule conjI, rule_tac x=True in exI, simp (no_asm))
    apply clarsimp
    apply(drule_tac x=i in spec, drule mp, assumption)+
    apply(subst (asm) HoareTripleRG_def)
    apply(drule_tac c="sqs!i" in subsetD, simp)
     apply(erule InitCond_mono, clarsimp)
     apply(drule spec, erule mp)
     apply(rule_tac x=i in exI, simp)
    apply clarify
    apply(drule TermCond_D)
    apply(drule_tac x="Parallel_ix sq - 1" in spec, 
          drule_tac P="Parallel_ix sq - 1 < length(sqs!i)" in mp, simp)
    apply(drule mp)
     apply(drule_tac x="Parallel_ix sq - 1" in spec, drule mp, rule conjI, simp, simp)
     apply(clarsimp simp: Parallel_simR_def)
    apply clarsimp
    apply(rename_tac l s tks)
    apply(frule_tac sq="sqs!i" in pcsD)
    apply(drule_tac sq="sqs!i" and Q="Q i" and i=l and j="Parallel_ix sq - 1" in Skip_COMP')
          apply(rename_tac n s' t' p tk1)
          apply(erule subsetD)
          apply(rule_tac a=s' in ImageI)
           apply(erule_tac sq="sqs!i" and i=n in EnvCond_D, assumption+, simp, assumption)
          apply assumption
         apply simp
        apply simp
       apply simp
      apply simp
     apply simp
    apply(drule_tac x="Parallel_ix sq - 1" in spec, drule mp, rule conjI, simp, simp)
    apply(clarsimp simp: Parallel_simR_def)
   apply(subgoal_tac "drop (Parallel_ix sq) sq \<in> \<lbrakk>Skip\<rbrakk>\<^sub>\<rho>")
    prefer 2
    apply(drule_tac su="drop (Parallel_ix sq) sq" in pcs_suffix_cls, rule suffix_drop, simp)
    apply clarsimp 
   apply(subst ProgCond_def, simp)
   apply(rule conjI, erule exI)
   apply(clarsimp simp: cstep_cond_def)
   apply(drule_tac t="sq!(i - Suc 0)" in sym)
   apply(case_tac "i = Parallel_ix sq", clarsimp simp: refl_on_def)
   apply(case_tac "Parallel_ix sq < i")
    apply(erule_tac i="i - Parallel_ix sq" in Skip_pcs_pstep, simp, simp, simp)
   apply(drule leI)
   apply(frule_tac x="i - 1" in spec, 
          drule_tac P="i - 1 < length sq \<and> i - 1 < Parallel_ix sq" in mp, fastforce)
   apply(drule_tac x="i" in spec, 
          drule_tac P="i < length sq \<and> i < Parallel_ix sq" in mp, fastforce)
   apply(clarsimp simp: Parallel_simR_def)
   apply(drule bspec, assumption)+
   apply(drule_tac x=x in mem_nth, clarsimp)
   apply(rename_tac n)
   apply(case_tac "sqs ! n ! (i - Suc 0)", clarsimp)
   apply(case_tac "sqs ! n ! i", clarsimp)
   apply(drule_tac x=n in spec, drule mp, assumption)+
   apply(subst (asm) HoareTripleRG_def)
   apply(drule_tac c="sqs!n" in subsetD, simp)
    apply(erule InitCond_mono, clarsimp)
    apply(drule spec, erule mp)
    apply(rule_tac x=n in exI, simp)
   apply clarify
   apply(drule_tac i=i in ProgCond_D, simp, assumption+)
   apply clarsimp
  apply(subgoal_tac "Parallel_ix sq = length sq")
   prefer 2
   apply(subst Parallel_ix_def, fastforce)
  apply clarsimp
  apply(rule conjI)
   apply(subst TermCond_def, simp)
   apply(rule conjI, erule exI)
   apply clarify
   apply(drule_tac x=j in spec, drule mp, assumption)
   apply(clarsimp simp: Parallel_simR_def)
  apply(subst ProgCond_def, simp)
  apply(rule conjI, erule exI)
  apply(clarsimp simp: cstep_cond_def)
  apply(drule_tac t="sq!(i - Suc 0)" in sym)
  apply(frule_tac x="i - 1" in spec,
          drule_tac P="i - 1 < length sq" in mp, fastforce)
  apply(drule_tac x="i" in spec,
          drule_tac P="i < length sq" in mp, fastforce)
  apply(clarsimp simp: Parallel_simR_def)
  apply(drule bspec, assumption)+
  apply(drule_tac x=x in mem_nth, clarsimp)
  apply(rename_tac n)
  apply(case_tac "sqs ! n ! (i - Suc 0)", clarsimp)
  apply(case_tac "sqs ! n ! i", clarsimp)
  apply(drule_tac x=n in spec, drule mp, assumption)+
  apply(subst (asm) HoareTripleRG_def)
  apply(drule_tac c="sqs!n" in subsetD, simp)
   apply(erule InitCond_mono, clarsimp)
   apply(drule spec, erule mp)
   apply(rule_tac x=n in exI, simp)
  apply clarify
  apply(drule_tac i=i in ProgCond_D, simp, assumption+)
  apply clarsimp
  done




subsection "A rule for Seq"


lemma SeqRule :
"\<rho> \<Turnstile> {R, P} p {V, G} \<Longrightarrow>
 \<rho> \<Turnstile> {R, V} q {Q, G} \<Longrightarrow>
 refl G \<Longrightarrow>
 (q = SKIP \<Longrightarrow> R `` Q \<subseteq> Q) \<Longrightarrow>
 \<rho> \<Turnstile> {R, P} (p;q) {Q, G}"
  apply(subst HoareTripleRG_def, clarify)
  apply(simp add: pcs_def InitCond_def)
  apply clarsimp
  apply(rename_tac sq s0 tk)
  apply(subgoal_tac "sq \<in> \<lbrakk>Seq p q\<rbrakk>\<^sub>\<rho>")
   prefer 2
   apply(simp add: pcs_def) 
  apply(frule COMP_noNil)
  apply(subst (asm) hd_conv_nth, assumption)
  apply(case_tac "\<not>(\<exists>j. j < length sq \<and> progOf(sq!j) = Skip;q)")
   apply simp
   apply(frule Seq_split, simp)
   apply clarify
   apply(rule conjI)
    apply(subst TermCond_def, simp)
    apply(erule exI)
   apply(subst (asm) HoareTripleRG_def[where p=p])
   apply(drule_tac c=sq1 in subsetD, simp)
    apply(rule conjI)
     apply(subst EnvCond_def, simp)
     apply(rule conjI, erule exI)
     apply(clarsimp simp: cstep_cond_def)
     apply(drule_tac x=i in spec, drule mp, assumption)
     apply(frule_tac x=i in spec, drule mp, assumption)
     apply(drule_tac x="i-1" in spec, drule mp, simp)
     apply(drule_tac t="sq1!(i - Suc 0)" in sym, clarsimp)
     apply(erule_tac i=i in EnvCond_D, simp, assumption+)
    apply(subst InitCond_def, simp)
    apply(rule conjI, erule exI)
    apply(subst hd_conv_nth, clarsimp)
    apply(drule_tac x="0" in spec, drule mp, simp)+
    apply(case_tac "sq1!0", clarsimp+)
   apply(subst ProgCond_def, simp)
   apply(rule conjI, erule exI)
   apply(clarsimp simp: cstep_cond_def)
   apply(drule_tac x=i in spec, drule mp, assumption)
   apply(frule_tac x=i in spec, drule mp, assumption)
   apply(drule_tac x="i-1" in spec, drule mp, simp)
   apply(case_tac "sq1!i", case_tac "sq1!(i-1)", clarsimp)
   apply(erule_tac i=i in ProgCond_D, simp, assumption+)
  apply(simp, erule exE)
  apply(drule_tac j=j and P="\<lambda>x. x < length sq \<and> progOf(sq!x) = Skip;q" in least_ix)
  apply clarsimp
  apply(case_tac "sq!i", clarsimp)
  apply(rename_tac t tk1)
  apply(subgoal_tac "take (i+1) sq \<in> \<lbrakk>Seq p q\<rbrakk>\<^sub>\<rho>")
   prefer 2
   apply(erule pcs_prefix_cls, rule prefix_take, simp)
  apply(drule_tac sq="take (i+1) sq" in Seq_split, fastforce)
  apply clarsimp
  apply(subgoal_tac "min (length sq) (Suc i) = Suc i")
   prefer 2
   apply(simp add: min_def)
  apply clarsimp
  apply(case_tac "sq1!i", clarsimp)
  apply(rename_tac t tk1)
  apply(subgoal_tac "t \<in> V \<and> take (i+1) sq \<in> ProgCond \<rho> G")
   prefer 2
   apply(subst (asm) HoareTripleRG_def)
   apply(drule_tac c=sq1 in subsetD, simp)
    apply(rule conjI)
     apply(subst EnvCond_def, simp)
     apply(rule conjI, erule exI)
     apply(rule allI, rename_tac k)
     apply(clarsimp simp: cstep_cond_def)
     apply(frule_tac x=k in spec, drule mp, simp)
     apply(drule_tac x="k-1" in spec, drule mp, rule conjI, simp, simp)
     apply(drule_tac t="sq1!(k - Suc 0)" in sym, clarsimp)
     apply(erule_tac i=k in EnvCond_D, simp, assumption+)
    apply(subst InitCond_def, simp)
    apply(rule conjI, erule exI)
    apply(subst hd_conv_nth, erule pcs_noNil)
    apply(drule_tac x="0" in spec, drule mp, simp)
    apply(case_tac "sq1!0", clarsimp+)
   apply(rule conjI)
    apply(frule_tac x=i in spec, drule mp, rule conjI, simp, simp)
    apply(drule TermCond_D)
    apply(drule_tac x=i in spec, drule_tac P="i<length sq1" in mp, simp)
    apply(drule mp, simp)
    apply clarsimp
    apply(rename_tac k t' tk')
    apply(case_tac "k = i", clarsimp)
    apply(drule_tac x=k in spec, drule mp, rule conjI, simp, simp)
    apply(drule_tac x=k in spec, drule_tac P="k<i" in mp, simp)
    apply clarsimp
   apply(subst ProgCond_def, simp)
   apply(rule conjI, rule exI, erule pcs_prefix_cls)
     apply(rule prefix_take, clarsimp)
   apply(rule allI, rename_tac k)
   apply(clarsimp simp: cstep_cond_def)
   apply(frule_tac x=k in spec, drule mp, rule conjI, simp, simp)
   apply(drule_tac x="k-1" in spec, drule mp, rule conjI, simp, simp)
   apply(case_tac "sq1!(k - 1)", case_tac "sq1!k", clarsimp)
   apply(erule_tac i=k in ProgCond_D, simp, assumption+)
  apply(subgoal_tac "drop i sq \<in> \<lbrakk>(SKIP;q)\<rbrakk>\<^sub>\<rho>")
   prefer 2
   apply(drule_tac sq=sq and su="drop i sq" in pcs_suffix_cls)
     apply(rule suffix_drop, simp)
   apply simp
  apply(case_tac "\<exists>j>i. j<length sq \<and> snd(sq!j)")
   prefer 2
   apply simp
   apply(drule_tac sq="drop i sq" and P=UNIV in esteps_pcs, clarsimp, simp (no_asm))
   apply clarsimp
   apply(rule conjI)
    apply(subst TermCond_def, clarsimp)
    apply(rule conjI, erule exI)
    apply clarsimp
    apply(rename_tac k)
    apply(case_tac "k \<le> i")
     apply(drule_tac x=k in spec, drule mp, erule conjI, simp+)
    apply(drule_tac x="k - i" in spec, drule_tac P="k-i<length sq-i" in mp, simp)
    apply simp
   apply(subst ProgCond_def, simp)
   apply(rule conjI, erule exI)
   apply(rule allI)
   apply(rename_tac k)
   apply(clarsimp simp: cstep_cond_def)
   apply(drule_tac t="sq!(k - Suc 0)" in sym)
   apply(case_tac "k \<le> i")
    apply(erule_tac i=k in ProgCond_D, simp, assumption, simp, simp)
   apply(drule_tac x=k in spec)+
   apply simp
  apply(erule exE)
  apply(drule_tac P="\<lambda>x. i < x \<and> x < length sq \<and> snd (sq ! x)" in least_ix)
  apply clarsimp
  apply(rename_tac i1)
  apply(subgoal_tac "take (i1-i) (drop i sq) \<in> \<lbrakk>(SKIP;q)\<rbrakk>\<^sub>\<rho>")
   prefer 2
   apply(erule pcs_prefix_cls, rule prefix_take, clarsimp)
  apply(frule_tac sq="take (i1-i) (drop i sq)" in Seq_split2)
   apply clarsimp
  apply clarsimp
  apply(subgoal_tac "length sq2 = i1 - i")
   prefer 2
   apply(erule_tac t="length sq2" in subst)
   apply(simp add: min_def)
  apply(thin_tac " min (length sq - i) (i1 - i) = length sq2")
  apply simp
  apply(frule_tac x="i1 - 1 - i" in spec, 
        drule_tac P="i1 - 1 - i < i1-i" in mp, simp)
  apply(case_tac "sq!i1", case_tac "sq!(i1-1)", clarsimp)
  apply(frule_tac sq=sq and i=i1 in pcs_nth, simp, simp)
  apply clarsimp
  apply(drule stepR_D1)
  apply(drule Seq_pstep_Skip, clarsimp)
  apply(subgoal_tac "sq2 @ tl(drop i1 sq) \<in> COMP \<rho>")
   prefer 2
   apply(rule COMP_compose')
     apply(drule pcsD, assumption)
    apply(erule COMP_suffix_cls, rule suffix_drop, clarsimp)
   apply(subst last_conv_nth, erule pcs_noNil)
   apply(subst hd_conv_nth, clarsimp)
   apply clarsimp
  apply(subgoal_tac "sq2 @ tl(drop i1 sq) \<in> \<lbrakk>q\<rbrakk>\<^sub>\<rho>")
   prefer 2
   apply(frule_tac sq=sq2 in pcs_noNil)
   apply(subst pcs_def, simp)
   apply(subst hd_conv_nth, simp)
   apply(erule_tac sq=sq2 in pcs0)
  apply(subgoal_tac "sq2 @ tl (drop i1 sq) \<in> EnvCond \<rho> R")
   prefer 2
   apply(thin_tac "\<forall>x. x < length sq \<and> x< Suc i \<longrightarrow> _ x ")
   apply(rule EnvCond_compose)
     apply(subst EnvCond_def, simp)
     apply(rule conjI, erule exI)
     apply(rule allI, rename_tac k)
     apply(clarsimp simp: cstep_cond_def)
     apply(frule_tac x=k in spec, drule mp, assumption)
     apply(drule_tac x="k-1" in spec, drule_tac P="k-1<i1 - i" in mp, simp)
     apply(case_tac "sq!(i+k-1)", case_tac "sq!(i+k)", clarsimp)
     apply(drule_tac x="i+k" in spec, simp)+
     apply(erule_tac i="i+k" in EnvCond_D, simp, simp, assumption+)
    apply(erule EnvCond_suffix_cls, rule suffix_drop, fastforce, rule subset_refl)
   apply(subst last_conv_nth, fastforce)
   apply clarsimp
   apply(subst hd_conv_nth, simp)
   apply clarsimp
  apply(subst (asm) HoareTripleRG_def[where p=q])
  apply(drule_tac c="sq2 @ tl(drop i1 sq)" in subsetD, simp)
   apply(subst InitCond_def, simp)
   apply(rule conjI, erule exI)
   apply(subst hd_conv_nth, erule COMP_noNil)
   apply(subst nth_append, simp)
  apply(rule conjI)
   apply(subst TermCond_def, simp)
   apply(rule conjI, erule exI)
   apply(rule allI, rename_tac k)
   apply clarify
   apply(case_tac "k \<le> i")
    apply(drule_tac x=k in spec, drule mp, rule conjI, clarsimp+)
   apply(drule not_le_imp_less)
   apply(case_tac "k < i1")
    apply(drule_tac x="k-i" in spec, drule_tac P="k-i<i1-i" in mp, simp)
    apply clarsimp
   apply(drule leI)
   apply(case_tac "q=Skip", clarsimp)
    apply(drule TermCond_D)
    apply(drule_tac x="i1 - Suc i" in spec,
        drule_tac P="i1-Suc i < length (sq2 @ tl (drop i1 sq))" in mp)
     apply simp
    apply(drule mp)
     apply(subst nth_append, simp)
     apply(clarify, erule notE, rule diff_less_mono2)
      apply(simp (no_asm))
     apply assumption
    apply clarsimp
    apply(rename_tac l t2 tk2)
    apply(subst (asm) nth_append, simp split: if_splits)
    apply(frule_tac sq=sq2 in pcsD)
    apply(drule_tac sq=sq2 and i=l and j="i1 - Suc i" and Q=Q in Skip_COMP')
          apply(rename_tac k s t' p' tk')
          apply(drule_tac R=R and sq="sq2 @ tl (drop i1 sq)" and pr=sq2 in EnvCond_prefix_cls)
             apply(subst prefix_def, rule exI, rule refl)
            apply(erule pcs_noNil)
           apply(rule subset_refl)
          apply(erule subsetD)
          apply(rule_tac a=s in ImageI)
           apply(erule_tac i=k and sq=sq2  in EnvCond_D, assumption+, simp, assumption)
          apply assumption
         apply simp
        apply simp
       apply simp
      apply simp
     apply assumption
    apply clarsimp
    apply(rule_tac x=i1 in exI, simp)
    apply(rule_tac x=True in exI, simp (no_asm))
   apply(case_tac "k=i1", clarsimp)
   apply(subgoal_tac "i1 + 1 \<le> k")
    prefer 2
    apply simp
   apply(drule_tac m="i1+1" and l="i+1" in diff_le_mono, simp)
   apply(drule TermCond_D)
   apply(drule_tac x="k-i-1" in spec, drule_tac P="k-i-1<length (sq2 @ tl (drop i1 sq))" in mp)
    apply simp
   apply(drule mp, simp)
    apply(subst nth_append, simp)
    apply(subst nth_tl, simp)
    apply simp
   apply(erule exE, rename_tac l)
   apply clarsimp
   apply(subst (asm) nth_append, simp split: if_splits)
   apply(drule leI)
   apply(subst (asm) nth_tl, simp)
   apply simp
   apply(rule_tac x="l+i+1" in exI, simp)
  apply(subgoal_tac "sq = take (i1 + 1) sq @ tl(drop i1 sq)")
   prefer 2
   apply(subst tl_drop)
   apply(subst drop_Suc[THEN sym])
   apply simp
  apply(erule_tac t=sq in ssubst)
  apply(rule ProgCond_compose, simp)
    apply(subgoal_tac "Suc i1 = Suc i + (i1 - i)")
     apply(erule_tac t="Suc i1" in ssubst)
     apply(subst take_add)
     apply(subst take_drop_tl[simplified], simp)
     apply(erule ProgCond_compose)
      apply(subst ProgCond_def, clarsimp)
      apply(rule conjI)
       apply(rule exI, rule pcs_prefix_cls[rotated 1], rule prefix_take, clarsimp, 
             rule pcs_suffix_cls[rotated 1], rule suffix_drop, clarsimp, assumption)
      apply(rule allI, rename_tac k)
      apply(clarsimp simp: cstep_cond_def)
      apply(case_tac "i+k=i1", clarsimp simp: refl_on_def)
      apply(drule_tac x="i+k" in spec, drule_tac P="i+k<i1" in mp, simp+)
     apply(subst last_conv_nth, simp)
     apply(subst hd_conv_nth, simp, simp, simp)
   apply clarify
   apply(drule ProgCond_decompose, simp, simp)
    apply(subst last_conv_nth, (drule pcs_noNil)+, simp)
    apply(subst hd_conv_nth, simp, simp, simp)
  apply(subst last_conv_nth, simp)
  apply(subst hd_conv_nth, (simp add: min_def)+)
  apply(clarify, subgoal_tac "length sq = i1 + 1", clarsimp+)
  done





end



















