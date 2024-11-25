(* *********************************************************************

    Theory Rules_prelims.thy is part of a framework for modelling,
    verification and transformation of concurrent imperative
    programs. Copyright (c) 2021  M. Bortin

    The framework is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.
    For more details see the license agreement (LICENSE) you should have
    received along with the framework.
    
   ******************************************************************* *)

theory Rules_prelims
imports RG
begin


lemma take_drop_tl :
"i+1 \<le> length xs \<Longrightarrow>
 take j (drop (i+1) xs) = tl(take (j+1) (drop i xs))"
  apply(rule nth_equalityI, simp+)
  apply(subst nth_tl, simp add: min_def)
  by simp


lemma drop_condsG :
"sq \<in> COMP \<rho> \<Longrightarrow>
 drop i sq \<in> TermCond \<rho> Q \<Longrightarrow>
 drop i sq \<in> ProgCond \<rho> G \<Longrightarrow> 
 \<forall>k<i. progOf (sq ! k) \<noteq> Skip \<Longrightarrow>
 take (i+1) sq \<in> ProgCond \<rho> G \<Longrightarrow>
 sq \<in> TermCond \<rho> Q \<and> sq \<in> ProgCond \<rho> G"
  apply(rule conjI)
   apply(subst TermCond_def, simp)
   apply(rule conjI, simp add: pcs_def)
    apply(subst hd_conv_nth, erule COMP_noNil)
    apply(case_tac "sq!0", fast)
   apply clarify
   apply(case_tac "j < i")
    apply(frule_tac x=j in spec, drule mp, simp, erule notE, assumption)
   apply(drule leI)
   apply(drule TermCond_D)
      apply(drule_tac x="j-i" in spec, drule mp, simp, drule mp, simp)
   apply clarsimp
   apply(rename_tac l t' tk'')
   apply(rule_tac x="i + l" in exI, simp)
  apply(subst ProgCond_def, simp)
  apply(rule conjI, simp add: pcs_def)
   apply(subst hd_conv_nth, erule COMP_noNil)
   apply(case_tac "sq!0", fast)
  apply(clarsimp simp: cstep_cond_def)
  apply(rename_tac k p1 s1 tk1 p2 s2 tk2)
  apply(drule_tac t="sq ! (k - Suc 0)" in sym)
  apply(case_tac "k \<le> i")
  apply(drule_tac i=k and sq="take (Suc i) sq" in ProgCond_D, fastforce, assumption, simp+)
  apply(erule_tac i="k - i" in ProgCond_D, simp+)
  done

corollary drop_conds :
"sq \<in> COMP \<rho> \<Longrightarrow>
 sq ! i = ((p', t), True) \<Longrightarrow>
 sq ! (i - Suc 0) = ((p, t), tk) \<Longrightarrow>
 drop i sq \<in> TermCond \<rho> Q \<Longrightarrow>
 drop i sq \<in> ProgCond \<rho> G \<Longrightarrow> 
 refl G \<Longrightarrow>
 0 < i \<Longrightarrow>
 \<forall>k<i. 0 < k \<longrightarrow> \<not> snd (sq ! k) \<Longrightarrow>
 \<forall>k<i. progOf (sq ! k) \<noteq> Skip \<Longrightarrow>
 sq \<in> TermCond \<rho> Q \<and> sq \<in> ProgCond \<rho> G"
  apply(frule COMP_noNil)
  apply(rule drop_condsG, assumption+)
  apply(subst ProgCond_def, simp)
  apply(rule conjI, simp add: pcs_def)
  apply(rule conjI, erule COMP_prefix_cls, rule prefix_take, simp+)
   apply(subst hd_conv_nth, simp+)
   apply(case_tac "sq!0", fast)
  apply(rule allI)
  apply(rename_tac j, clarsimp simp: cstep_cond_def)
  apply(case_tac "j = i", clarsimp simp: refl_on_def)
  by (metis less_antisym snd_conv)

corollary drop_conds' :
"sq \<in> COMP \<rho> \<Longrightarrow>
 drop i sq \<in> TermCond \<rho> Q \<Longrightarrow>
 drop i sq \<in> ProgCond \<rho> G \<Longrightarrow> 
 \<forall>k\<le>i. 0 < k \<longrightarrow> \<not>tkOf(sq!k) \<Longrightarrow>
 \<forall>k<i. progOf(sq!k) \<noteq> Skip \<Longrightarrow>
 sq \<in> TermCond \<rho> Q \<and> sq \<in> ProgCond \<rho> G"
  apply(frule COMP_noNil)
  apply(rule drop_condsG, assumption+)
  apply(subst ProgCond_def, simp)
  apply(rule conjI, simp add: pcs_def)
  apply(rule conjI, erule COMP_prefix_cls, rule prefix_take, simp+)
   apply(subst hd_conv_nth, simp+)
   apply(case_tac "sq!0", fast)
  apply(rule allI)
  apply(rename_tac j, clarsimp simp: cstep_cond_def)
  by (metis less_Suc_eq_le snd_conv)



section "Seq splits"


lemma Seq_split[rule_format] :
"sq \<in> \<lbrakk>Seq p1 p2\<rbrakk>\<^sub>\<rho> \<Longrightarrow> 
 \<forall>i<length sq. 0 < i \<longrightarrow> tkOf(sq!i) \<longrightarrow> progOf(sq!(i-1)) \<noteq> Seq Skip p2 \<Longrightarrow>
 \<exists>sq1. length sq1 = length sq \<and> 
   sq1 \<in> \<lbrakk>p1\<rbrakk>\<^sub>\<rho> \<and> 
   (\<forall>i<length sq. sq!i = ((Seq (progOf(sq1!i)) p2, stateOf(sq1!i)), tkOf(sq1!i)))"
  apply(frule pcs_noNil)
  apply(subgoal_tac "\<forall>i<length sq. \<exists>u. progOf(sq!i) = Seq u p2")
  apply(rule_tac x="fprefix (\<lambda>i. case (sq!i) of
                                 ((Seq u p2, s), tk) \<Rightarrow> ((u, s), tk)) (length sq)" in exI, 
        simp add: fprefix_length)
   apply(rule conjI)
    apply(clarsimp simp: pcs_def)
    apply(rule conjI)
     apply(subst COMP_eq, simp add: fprefix_length fprefix_nth)
     apply(rule conjI, clarsimp)
      apply(drule_tac f=length in arg_cong, simp add: fprefix_length)
     apply clarsimp
     apply(frule_tac x=i in spec, drule mp, simp, erule exE)
     apply(drule_tac x="i+1" in spec, drule mp, simp, erule exE)
     apply(case_tac "sq!i", case_tac "sq!(i+1)", clarsimp)
     apply(drule_tac i="i+1" in COMP_nth, simp, simp)
     apply clarsimp
     apply(rename_tac tk)
     apply(case_tac tk, simp)
      apply(drule stepR_D1)
      apply(drule Seq_pstep, clarsimp)
       apply(drule_tac x="i+1" in spec, simp)
      apply(clarsimp simp: stepR_def, rule_tac x=True in exI, simp (no_asm))
     apply(clarsimp, drule stepR_D2, clarsimp simp: stepR_def, rule_tac x=False in exI, simp (no_asm))
    apply(subst hd_conv_nth)
     apply(clarsimp, drule_tac f=length in arg_cong, simp add: fprefix_length)
    apply(simp add: fprefix_nth)
    apply(subst (asm) hd_conv_nth, simp)
    apply fastforce
   apply(clarsimp simp: fprefix_nth)
   apply(case_tac "sq!i", clarsimp)
   apply(drule_tac x=i in spec, drule mp, assumption, erule exE)
   apply clarsimp
  apply(rule allI)
  apply(induct_tac i, clarsimp simp: pcs_def)
   apply(rule_tac x=p1 in exI)
   apply(subst (asm) hd_conv_nth, simp+)
  apply clarsimp
  apply(case_tac "sq!n", case_tac "sq!(n+1)", clarsimp)
  apply(rename_tac tk)
  apply(drule_tac i="n+1" in pcs_nth, simp+)
  apply(case_tac tk, simp)
   apply(drule_tac x="n+1" in spec, clarsimp)
   apply(drule stepR_D1)
   apply(drule Seq_pstep, assumption, fast)
  apply(simp, drule stepR_D2, fast)
  done


lemma Seq_split_ext[rule_format] :
"sq \<in> \<lbrakk>Seq p1 p2\<rbrakk>\<^sub>\<rho> \<Longrightarrow> sq \<in> EnvCond \<rho> R \<Longrightarrow> sq \<in> InitCond \<rho> P \<Longrightarrow>
 \<forall>i<length sq. 0 < i \<longrightarrow> tkOf(sq!i) \<longrightarrow> progOf(sq!(i-1)) \<noteq> Seq Skip p2 \<Longrightarrow>
 \<exists>sq1. length sq1 = length sq \<and> 
   sq1 \<in> \<lbrakk>p1\<rbrakk>\<^sub>\<rho> \<and> sq1 \<in> EnvCond \<rho> R \<and> sq1 \<in> InitCond \<rho> P \<and>
   (\<forall>i<length sq. sq!i = ((Seq (progOf(sq1!i)) p2, stateOf(sq1!i)), tkOf(sq1!i)))"
  apply(frule Seq_split, clarsimp+)
  apply(rule_tac x=sq1 in exI, simp)
  apply(rule conjI)
   apply(subst EnvCond_def, simp)
   apply(rule conjI, erule exI)
   apply(clarsimp simp: cstep_cond_def)
   apply(drule_tac x=i in spec, drule mp, assumption)
   apply(frule_tac x=i in spec, drule mp, assumption)
   apply(drule_tac x="i-1" in spec, drule mp, simp)
   apply(drule_tac t="sq1!(i - Suc 0)" in sym, clarsimp)
   apply(erule_tac i=i in EnvCond_D, simp+)
  apply(clarsimp simp: InitCond_def)
  apply(frule pcs_noNil)
  by (metis fst_conv hd_conv_nth length_0_conv not_gr_zero snd_conv surjective_pairing)



lemma Seq_split2[rule_format] :
"sq \<in> \<lbrakk>Seq Skip p2\<rbrakk>\<^sub>\<rho> \<Longrightarrow> 
 \<forall>i<length sq. 0 < i \<longrightarrow> \<not>tkOf(sq!i) \<Longrightarrow>
 \<exists>sq2. length sq = length sq2 \<and> 
   sq2 \<in> \<lbrakk>p2\<rbrakk>\<^sub>\<rho> \<and> 
   (\<forall>i<length sq2. progOf(sq!i) = Skip;p2 \<and> sq2!i = ((p2, stateOf(sq!i)), tkOf(sq!i)))"
  apply(frule pcs_noNil)
  apply(subgoal_tac "\<forall>i<length sq. progOf(sq!i) = Seq Skip p2")
  apply(rule_tac x="fprefix (\<lambda>i. case (sq!i) of
                                 ((Seq u p, s), tk) \<Rightarrow> ((p, s), tk)) (length sq)" in exI, 
        simp add: fprefix_length)
   apply(rule conjI)
    apply(clarsimp simp: pcs_def)
    apply(rule conjI)
     apply(subst COMP_eq, simp add: fprefix_length fprefix_nth)
     apply(rule conjI, clarsimp)
      apply(drule_tac f=length in arg_cong, simp add: fprefix_length)
     apply clarsimp
     apply(drule_tac x="i+1" in spec, drule mp, simp+)
     apply(frule_tac x=i in spec, drule mp, simp)
     apply(drule_tac x="i+1" in spec, drule mp, simp)
     apply(case_tac "sq!i", case_tac "sq!(i+1)", clarsimp)
     apply(drule_tac i="i+1" in COMP_nth, simp, simp)
     apply clarsimp
     apply(subst stepR_def, simp, rule_tac x=False in exI, simp (no_asm))
    apply(subst hd_conv_nth)
     apply(clarsimp, drule_tac f=length in arg_cong, simp add: fprefix_length)
    apply(simp add: fprefix_nth)
    apply(subst (asm) hd_conv_nth, simp)
    apply fastforce
   apply(clarsimp simp: fprefix_nth)
   apply(case_tac "sq!i", clarsimp)
   apply(drule_tac x=i in spec, drule mp, assumption)+
   apply clarsimp
  apply(rule allI)
  apply(induct_tac i, clarsimp simp: pcs_def)
   apply(subst (asm) hd_conv_nth, simp+)
  apply clarsimp
  apply(case_tac "sq!n", case_tac "sq!(n+1)", clarsimp)
  apply(drule_tac x="n+1" in spec, simp)
  apply(drule_tac i="n+1" in pcs_nth, simp+)
  apply(drule stepR_D2, clarsimp)
  done


lemma Seq_split2_ext[rule_format] :
"sq \<in> \<lbrakk>Seq Skip p2\<rbrakk>\<^sub>\<rho> \<Longrightarrow> sq \<in> EnvCond \<rho> R \<Longrightarrow> 
 \<forall>i<length sq. 0 < i \<longrightarrow> \<not>tkOf(sq!i) \<Longrightarrow>
 \<exists>sq2. length sq = length sq2 \<and> 
   sq2 \<in> \<lbrakk>p2\<rbrakk>\<^sub>\<rho> \<and> sq2 \<in> EnvCond \<rho> R \<and>
   (\<forall>i<length sq2. progOf(sq!i) = Skip;p2 \<and> sq2!i = ((p2, stateOf(sq!i)), tkOf(sq!i)))"
  apply(frule Seq_split2, clarsimp+)
  apply(rule_tac x=sq2 in exI, simp)
  apply(subst EnvCond_def, simp)
  apply(rule conjI, erule exI)
  apply(clarsimp simp: cstep_cond_def)
  apply(drule_tac x=i in spec, drule mp, assumption)
  apply(frule_tac x=i in spec, drule mp, assumption)
  apply(drule_tac x="i-1" in spec, drule mp, simp)
  apply(case_tac "sq!(i-1)")
  apply(case_tac "sq!i", clarsimp)
  apply(erule_tac i=i in EnvCond_D, simp+)
  done


section "Splitting parallel computations"


definition "Parallel_break = {(((Parallel ps, s), tk), ((p, s), True)) | ps p s tk. p = Skip}"


lemma Parallel_breakD :
"(a, b) \<in> Parallel_break \<Longrightarrow> \<exists>ps s tk p. a = ((Parallel ps, s), tk) \<and> b = ((p, s), True) \<and> p = Skip"
by(simp add: Parallel_break_def) 

definition stepRP :: "(nat \<Rightarrow> 's LA) \<Rightarrow> (('s config \<times> bool) \<times> ('s config \<times> bool)) set"
where "stepRP \<rho> = stepR \<rho> - Parallel_break"



definition Parallel_simR :: "(('s config \<times> bool) list \<times> ('s config \<times> bool)) set"
where "Parallel_simR = {(xs, ((Parallel ps, s), tk)) | xs ps s tk.
                  length xs = length ps \<and> (\<forall>i<length ps. progOf(xs!i) = fst(ps!i)) \<and> 
                                          (\<forall>cf\<in>set xs. stateOf cf = s) \<and> 
                  tk = (\<exists>cf\<in>set xs. tkOf cf)}"


lemma Parallel_simR_D :
"(xs, ((p, s), tk)) \<in> Parallel_simR \<Longrightarrow>
 (\<exists>ps. p = Parallel ps \<and> 
      length xs = length ps \<and> (\<forall>i<length ps. progOf(xs!i) = fst(ps!i))) \<and>
(\<forall>cf \<in> set xs. stateOf cf = s) \<and> 
 tk = (\<exists>cf \<in> set xs. tkOf cf)"
  by(simp add: Parallel_simR_def, blast)


lemma Parallel_simR_InitCond :
"sq \<in> InitCond \<rho> A \<Longrightarrow>
 \<forall>n<length sqs. length(sqs!n) = length sq \<and> sqs!n \<in> \<lbrakk>fst(ps!n)\<rbrakk>\<^sub>\<rho> \<Longrightarrow>
 0 < length sq \<Longrightarrow> 
 \<forall>m<length sq. (map (\<lambda>x. x!m) sqs, sq!m) \<in> Parallel_simR \<Longrightarrow>
 \<forall>n<length sqs. sqs!n \<in> InitCond \<rho> A"
  apply(clarsimp simp add: InitCond_def)
  apply(drule spec, drule mp, assumption)
  apply clarify
  apply(rule conjI, erule exI)
  apply(subst hd_conv_nth, fastforce)
  apply(subst (asm) hd_conv_nth, assumption) 
  apply(drule_tac x=0 in spec, clarsimp simp add: Parallel_simR_def)
  apply(drule_tac x="sqs!n" in bspec)
  apply(rule nth_mem, simp)
  apply(case_tac "sqs!n!0", clarsimp)
  done

 

text "This is auxiliary"
definition step2 :: "('a \<times> 'a) set \<Rightarrow> ('a list \<times> 'a list) set"
where "step2 R = {(xs, xs') | xs xs'. length xs = length xs' \<and> (\<forall>(x, x')\<in>set(zip xs xs'). (x, x') \<in> R)}"


lemma Parallel_simR :
"Parallel_simR O stepRP \<rho> \<subseteq> step2 (stepR \<rho>) O Parallel_simR"
  apply(simp add: Parallel_simR_def step2_def)
  apply clarsimp
  apply(rename_tac p' s' tk' xs ps s)
  apply(simp add: stepRP_def Parallel_break_def)
  apply(case_tac tk', clarsimp)
   apply(drule stepR_D1)
   apply(drule Parallel_pstep)
   apply(erule disjE, clarsimp)
    apply(rule_tac b="(map (\<lambda>((p, s), tk). ((p, s'), False)) xs)[i := ((p'', s'), True)]" in relcompI)
     apply clarsimp
     apply(drule zip_nthD)
     apply clarsimp
     apply(rename_tac j)
     apply(drule sym)
     apply(case_tac "i = j", clarsimp)
      apply(drule_tac x="xs!j" in bspec, erule nth_mem)
      apply(simp add: stepR_def)
      apply(intro exI, rule conjI, rule exI, erule sym)
      apply(rule_tac x=True in exI)
      apply(drule_tac x=j in spec, drule mp, assumption)
      apply(drule_tac t="xs!j" in sym)
      apply clarsimp
     apply clarsimp
     apply(drule_tac x="xs!j" in bspec, erule nth_mem)
     apply(simp add: stepR_def)
     apply(intro exI, rule conjI, rule exI, erule sym)
     apply(drule_tac t="xs!j" in sym)
     apply clarsimp
     apply fast
    apply clarsimp
    apply(rule conjI)
     apply(rule_tac x="((p'', s'), True)" in bexI, simp)
     apply(rule List.set_update_memI)
     apply simp
    apply(rule conjI)
     apply clarsimp
     apply(rename_tac j)
     apply(case_tac "j = i", clarsimp)
     apply clarsimp
     apply(drule_tac x=j in spec, simp)
     apply(case_tac "xs!j", clarsimp)
    apply clarsimp
    apply(drule subsetD[OF set_update_subset_insert], clarsimp)
    apply(erule disjE, simp)
    apply clarsimp
   apply clarsimp
  apply clarsimp
  apply(drule stepR_D2, clarsimp)
  apply(rule_tac b="map (\<lambda>((p, s), tk). ((p, s'), False)) xs" in relcompI)
   apply(clarsimp simp: stepR_def)
   apply(drule zip_nthD)
   apply clarsimp
   apply(drule sym, clarsimp)
   apply(drule_tac x="xs!i" in bspec, erule nth_mem)
   apply(rule exI, rule exI, rule exI, rule exI, rule exI, rule_tac x=False in exI, simp)
   apply(rule conjI, rule refl)+
   apply(case_tac "xs!i", clarsimp)
  apply clarsimp
  apply(rule conjI, clarsimp)
  apply(rule conjI, clarsimp)
   apply(case_tac "xs!i", fastforce)
  apply clarsimp
  done
 


definition "Parallel_ix sq = 
(if (\<exists>j<length sq. 0<j \<and> (sq!(j-1), sq!j) \<in> Parallel_break)
 then (LEAST j. j<length sq \<and> 0<j \<and> (sq!(j-1), sq!j) \<in> Parallel_break)
 else length sq)"

lemma Parallel_ix_le :
"Parallel_ix sq \<le> length sq"
  apply(clarsimp simp: Parallel_ix_def)
  apply(rule_tac a=j in LeastI2, simp_all)
 done

corollary Parallel_ix_min: 
"min (length sq) (Parallel_ix sq) = Parallel_ix sq"
  apply(insert Parallel_ix_le[of sq])
  by(simp add: min_def)

lemma Parallel_ix_gr :
"sq \<noteq> [] \<Longrightarrow> 0 < Parallel_ix sq"
  apply(clarsimp simp: Parallel_ix_def)
  apply(rule_tac a=j in LeastI2, simp_all)
 done

lemma Parallel_ix_take :
"sq \<noteq> [] \<Longrightarrow> take (Parallel_ix sq) sq \<noteq> []"
  apply(simp add: Parallel_ix_def)
  apply clarsimp
  by(rule_tac a=j in LeastI2, clarsimp+)


lemma Parallel_ix_break :
"(sq!(j-1), sq!j) \<in> Parallel_break \<Longrightarrow> j < length sq \<Longrightarrow> 0 < j \<Longrightarrow>
 (sq!(Parallel_ix sq - 1), sq!(Parallel_ix sq)) \<in> Parallel_break \<and> Parallel_ix sq \<le> j" 
  apply(clarsimp simp: Parallel_ix_def)
  apply(rule conjI, clarify)
   apply(rule conjI)
    apply(rule_tac a=j in LeastI2, simp_all)
   apply(rule ccontr, drule not_le_imp_less)
   apply(drule not_less_Least, simp)
  apply fastforce
  done  


lemma Parallel_ix_least :
"k < Parallel_ix sq \<Longrightarrow> 0 < k \<Longrightarrow> 
 (sq!(k-1), sq!k) \<notin> Parallel_break"
  apply(subgoal_tac "k < length sq")
   apply(clarsimp simp: Parallel_ix_def)
   apply(simp split: if_split_asm)
    apply(drule not_less_Least, simp)
   apply fastforce
  apply(erule less_le_trans)
  by(rule Parallel_ix_le)
 



lemma Parallel_split' :
"sq \<in> COMP \<rho> \<Longrightarrow> 
 \<forall>ps s tk. hd sq = ((Parallel ps, s), tk) \<longrightarrow> 0 < length ps \<longrightarrow>
 (\<forall>i<length sq. 0 < i \<longrightarrow> (sq!(i-1), sq!i) \<notin> Parallel_break) \<longrightarrow>
 (\<exists>sqs. length sqs = length ps \<and> 
  (\<forall>n<length sqs. length(sqs!n) = length sq \<and> sqs!n \<in> \<lbrakk>fst(ps!n)\<rbrakk>\<^sub>\<rho>) \<and> 
  (\<forall>m<length sq. (map (\<lambda>x. x!m) sqs, sq!m) \<in> Parallel_simR))"
  apply(induct sq rule: rev_induct, drule COMP_noNil, clarify)
  apply(rename_tac sq)
  apply(case_tac "sq = []", clarsimp)
   apply(rule_tac x="map (\<lambda>p. [((fst p, s), tk)]) ps" in exI, simp add: Parallel_simR_def)
   apply(rule conjI)
    apply(clarsimp simp: pcs_def COMP_eq)
   apply(case_tac tk; clarsimp)
   apply(drule hd_Cons_tl, erule subst, simp)
   apply(case_tac "hd ps", clarsimp)
   apply fastforce
  apply clarsimp
  apply(rename_tac p' s' tk' sq ps s tk)
  apply(drule meta_mp)
  apply(erule_tac pr=sq in COMP_prefix_cls, simp add:prefix_def, assumption)
  apply(drule mp, clarsimp)
   apply(drule_tac x=i in spec, drule mp, simp+)
   apply(subst (asm) nth_append, simp)
   apply(subst (asm) nth_append, simp split: if_splits)
  apply clarsimp
  apply(insert Parallel_simR[of \<rho>])
  apply(drule_tac c="(map (\<lambda>x. x!(length sq - 1)) sqs, ((p', s'), tk'))" in subsetD)
   apply(rule_tac b="sq!(length sq - 1)" in relcompI)
    apply fastforce
   apply(clarsimp simp: stepRP_def)
   apply(drule_tac x="length sq" in spec, simp)
   apply(drule_tac i="length sq" in COMP_nth, simp+)
   apply(subst (asm) nth_append, simp split: if_splits)
   apply(subst (asm) nth_append, simp split: if_splits)
  apply clarsimp
  apply(rename_tac ps' p' s' tk')
  apply(rule_tac x="map (\<lambda>(x, sq). sq@[x]) (zip ps' sqs)" in exI, simp)
  apply(clarsimp simp: step2_def)
  apply(drule Parallel_simR_D, clarsimp)
  apply(rule conjI)
   apply(clarsimp simp add: pcs_def)
   apply(drule_tac x=n in spec, drule mp, assumption)
   apply clarsimp
   apply(frule_tac sq="sqs!n" in COMP_noNil)
   apply(rule conjI)
    apply(case_tac "ps'!n", clarsimp)
    apply(erule COMP_compose2)
    apply(subst last_conv_nth, assumption)
    apply(simp (no_asm) add: COMP_eq)
    apply(drule bspec)
     prefer 2
     apply assumption
    apply(subst in_set_zip)
    apply(rule_tac x=n in exI, simp)
   apply(subst hd_append, simp)
  apply clarsimp
  apply(case_tac "m = length sq", clarsimp)
   apply(subst Parallel_simR_def, simp)
   apply(rule conjI)
    apply(rule iffI, erule bexE)
     apply(rule_tac xs=ps' and ys=sqs and x=x in in_set_impl_in_set_zip1, simp, assumption)
     apply(rename_tac u v)
     apply(rule_tac x="(u, v)" in bexI, clarsimp)
      apply(frule zip_nthD, clarsimp)
      apply(drule_tac x=i in spec, drule mp, assumption, erule conjE)
      apply(subst nth_append, clarsimp)
      apply(erule_tac t="ps'!i" in subst,simp (no_asm))
     apply assumption
    apply clarsimp
    apply(frule zip_nthD, clarsimp)
    apply(drule_tac x=i in spec, drule mp, assumption, erule conjE)
    apply(subst (asm) nth_append, simp)+
    apply(erule_tac x="ps'!i" in bexI)
    apply(rule nth_mem, simp)
   apply(rule conjI, clarify)
    apply(drule_tac x=i in spec, drule mp, assumption)+
    apply(subst nth_append, simp)
   apply clarsimp
   apply(frule zip_nthD, clarsimp)
   apply(drule_tac x=i in spec, drule mp, assumption)
   apply(subst nth_append, simp)
   apply(subgoal_tac "m < length sq")
    prefer 2
    apply simp
   apply(thin_tac "m < Suc (length sq)")
   apply(subst map_zip_aux2[rotated 1], assumption, simp)
    apply clarify
    apply(drule mem_nth, clarsimp)
   apply(subst nth_append, simp)
  done



theorem Parallel_split[rule_format] :
"sq \<in> \<lbrakk>Parallel ps\<rbrakk>\<^sub>\<rho> \<Longrightarrow> 0 < length ps \<Longrightarrow>
 \<forall>i<length sq. 0 < i \<longrightarrow> (sq!(i-1), sq!i) \<notin> Parallel_break \<Longrightarrow>
 \<exists>sqs. length sqs = length ps \<and> 
  (\<forall>n<length sqs. length(sqs!n) = length sq \<and> sqs!n \<in> \<lbrakk>fst(ps!n)\<rbrakk>\<^sub>\<rho>) \<and> 
  (\<forall>m<length sq. (map (\<lambda>x. x!m) sqs, sq!m) \<in> Parallel_simR)"
  apply(subst (asm) pcs_def)
  apply clarsimp
  apply(drule Parallel_split'[rule_format], assumption, simp, clarsimp)
  by assumption





end

    