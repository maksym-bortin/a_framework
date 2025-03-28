(* *********************************************************************

    Theory Fairness.thy is part of a framework for modelling,
    verification and transformation of concurrent imperative
    programs. Copyright (c) 2021  M. Bortin

    The framework is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.
    For more details see the license agreement (LICENSE) you should have
    received along with the framework.
    
   ******************************************************************* *)

theory Fairness
imports Positions 
begin

subsection "Always available program positions"

text "defines positions that are generally available for a reduction so that 
      the subsequently presented notion of fairness gets comparably weak 
      as it does not address evaluation of await-statements 
      except terminating atomic sections"
definition "available_pos \<rho> p = {xs. xs \<in> set(rpos p) \<and> 
                                (case p|\<^bsub>xs\<^esub> of
                                  Some (Await C a p) \<Rightarrow> (C = UNIV \<and> (\<forall>s. \<exists>t. \<rho> \<turnstile> (p, s) -p\<rightarrow>\<^sup>* (Skip, t)))
                                | _ \<Rightarrow> True)}"
lemma available_rpos :
"xs \<in> available_pos \<rho> p \<Longrightarrow> 
 xs \<in> set(rpos p)"
  by(simp add: available_pos_def)


lemma available_pos_pstep' :
"xs \<in> available_pos \<rho> p \<Longrightarrow>
 \<exists>p' t. \<rho> \<turnstile> (the(p|\<^bsub>xs\<^esub>), s) -p\<rightarrow> (p', t)" 
  apply(clarsimp simp: available_pos_def)
  apply(induct p xs rule: lookup_pos.induct)
    apply(drule rpos_noNil, clarify)
   apply(frule rpos_singleton)
   apply clarsimp
   apply(case_tac p, clarsimp+)
         apply(intro exI, rule pstep.Basic)
        apply(clarsimp split: if_splits)
         apply(intro exI, rule pstep.SeqSkip)
        apply(drule rpos_noNil, clarify)
       apply clarsimp
       apply(rename_tac C p q)
       apply(case_tac "s \<in> C")
        apply(intro exI, erule pstep.CondT)
       apply(intro exI, erule pstep.CondF)
      apply clarsimp
      apply(rename_tac C I p q)
      apply(case_tac "s \<in> C")
       apply(intro exI, erule pstep.WhileT)
      apply(intro exI, erule pstep.WhileF)
     apply(clarsimp split: if_splits)
     apply(intro exI, rule pstep.ParallelSkip, fastforce)
    apply clarsimp
    apply(drule_tac x=s in spec, clarify)
    apply(intro exI, rule pstep.Await, simp+)
   apply(rename_tac C p q)
   apply(case_tac "s \<in> C")
    apply(intro exI, erule CJumpT)
   apply(intro exI, erule CJumpF)
  apply(rename_tac x' xs)
  apply clarsimp
  apply(rule conjI, clarsimp)
   apply(case_tac p, simp_all)
    apply(clarsimp split: if_splits)+
  apply(case_tac p, simp_all)
   apply(clarsimp split: if_splits)+
  done

text "thus, the subterm at an available position always amounts to a program step"
corollary available_pos_pstep :
"xs \<in> available_pos \<rho> p \<Longrightarrow>
 \<exists>p' t. \<rho> \<turnstile> (the(lookup_pos p xs), s) -p\<rightarrow> (p', t) \<and>
        \<rho> \<turnstile> (p, s) -p\<rightarrow> (p\<lbrakk>p'\<rbrakk>\<^bsub>xs\<^esub>, t)"
  apply(frule_tac s=s in available_pos_pstep')
  apply clarify
  apply(drule available_rpos)
  apply(drule rpos_pstep, assumption)
  by fast



lemma iCOMP_available_pos_retain :
"sq \<in> iCOMP \<rho> \<Longrightarrow> fair_ret \<rho> \<Longrightarrow> xs\<in>available_pos \<rho> (progOf(sq i)) \<Longrightarrow> i < j \<Longrightarrow>
 \<forall>k\<ge>i. k < j \<longrightarrow> tkOf(sq(k+1)) \<longrightarrow> (progOf(sq k))|\<^bsub>xs\<^esub> = (progOf(sq i))|\<^bsub>xs\<^esub> \<longrightarrow> 
        fpos_of \<rho> (confOf(sq k)) (confOf(sq(k+1))) \<noteq> xs \<Longrightarrow>
 xs\<in>available_pos \<rho> (progOf(sq j)) \<and> (progOf(sq i))|\<^bsub>xs\<^esub> = (progOf(sq j))|\<^bsub>xs\<^esub>"
  apply(drule_tac xs=xs in iCOMP_rpos_retain, assumption)
     apply(erule available_rpos)
    apply assumption+
  apply(clarsimp simp: available_pos_def)
  done



subsection "Fair potential computations"


definition
"fair_iCOMP \<rho> = {sq. sq \<in> iCOMP \<rho> \<and> 
 (\<forall>i. (\<forall>xs\<in>available_pos \<rho> (progOf(sq i)). 
  \<exists>j\<ge>i. tkOf(sq(j+1)) \<and> (progOf(sq j))|\<^bsub>xs\<^esub> = (progOf(sq i))|\<^bsub>xs\<^esub> \<and> 
        fpos_of \<rho> (confOf(sq j)) (confOf(sq(j+1))) = xs))}"


lemma fair_iCOMP_D1 :
"sq \<in> fair_iCOMP \<rho> \<Longrightarrow> sq \<in> iCOMP \<rho>"
  by(simp add: fair_iCOMP_def)

lemma fair_iCOMP_D2 :
"sq \<in> fair_iCOMP \<rho> \<Longrightarrow> xs \<in> available_pos \<rho> (progOf(sq i)) \<Longrightarrow> 
  \<exists>j\<ge>i. tkOf(sq(j+1)) \<and> (progOf(sq j))|\<^bsub>xs\<^esub> = (progOf(sq i))|\<^bsub>xs\<^esub> \<and> 
        fpos_of \<rho> (confOf(sq j)) (confOf(sq (j+1))) = xs"
  by(simp add: fair_iCOMP_def)


lemma fair_iCOMP_isuffix :
"sq \<in> fair_iCOMP \<rho> \<Longrightarrow> isuffix sq d \<in> fair_iCOMP \<rho>"
  apply(clarsimp simp: fair_iCOMP_def)
  apply(rule conjI)
   apply(erule iCOMP_isuffix)
  apply clarsimp
  apply(drule_tac x="i+d" in spec)
  apply(clarsimp simp: isuffix_def)
  apply(drule bspec, assumption)
  apply clarsimp
  apply(rule_tac x="j-d" in exI, simp)
  done


lemma isuffix_fair_iCOMP :
"isuffix sq d \<in> fair_iCOMP \<rho> \<Longrightarrow> sq \<in> iCOMP \<rho> \<Longrightarrow> fair_ret \<rho> \<Longrightarrow> sq \<in> fair_iCOMP \<rho>"
  apply(subst fair_iCOMP_def, clarsimp)
  apply(case_tac "i \<ge> d")
   apply(drule_tac i="i-d" and xs=xs in fair_iCOMP_D2)
    apply(clarsimp simp: isuffix_def)+
   apply(rule_tac x="j+d" in exI, simp)
  apply(rule ccontr)
  apply(drule_tac i=i and j=d in iCOMP_available_pos_retain)
      apply assumption+
    apply fastforce+
  apply(drule_tac i=0 and xs=xs in fair_iCOMP_D2)
   apply(clarsimp simp: isuffix_def)
  apply(drule not_le_imp_less)
  apply(erule notE)
  apply clarify
  apply(rule_tac x="j+d" in exI)
  apply(clarsimp simp: isuffix_def)
  done



subsection "A construction of fair computations"

text "this simple construction just keeps evaluating
      the given program p in a state s as long as an
      available position is present and yields to the 
      'stuttering' environment otherwise, which is fair
      if there cannot be more than one available position
      (this is the case with locally sequential jumpfree programs)"
fun fair_seq where
"fair_seq \<rho> p s 0 = ((p, s), True)" |
"fair_seq \<rho> p s (Suc n) = 
 (let ((p', s'), tk) = fair_seq \<rho> p s n in
  if \<exists>xs. xs \<in> available_pos \<rho> p' 
  then (SOME x. \<rho> \<turnstile> (p', s') -p\<rightarrow> x, True)
  else ((p', s'), False))"



lemma fair_seq_iCOMP :
"fair_seq \<rho> p s \<in> iCOMP \<rho>"
  apply(clarsimp simp: iCOMP_def)
  apply(case_tac "fair_seq \<rho> p s i", clarsimp)
  apply(rename_tac p' t tk)
  apply(rule conjI, clarsimp)
  apply(frule_tac s=t in available_pos_pstep)
   apply clarify
   apply(rename_tac q t')
   apply(rule_tac a="(p'\<lbrakk>q\<rbrakk>\<^bsub>xs\<^esub>, t')" in someI2)
    apply assumption
   apply(clarsimp simp: stepR_def)
   apply(rule_tac x=True in exI, simp)
  apply(clarsimp simp: stepR_def)
  apply(rule_tac x=False in exI, simp)
  done

 

lemma locally_seq_jumpfree_fair_ex : 
"locally_seq p \<Longrightarrow> jumpfree p \<Longrightarrow> fair_ret \<rho> \<Longrightarrow>
 \<forall>\<sigma>. \<exists>sq\<in>fair_iCOMP \<rho> \<inter> EnvCond_i \<rho> Id. confOf(sq 0) = (p, \<sigma>) "
  apply(rule allI)
  apply(rule_tac x="fair_seq \<rho> p \<sigma>" in bexI, simp+)
  apply(rule conjI, clarsimp simp: fair_iCOMP_def)
   apply(rule conjI)
    apply(rule fair_seq_iCOMP)
   apply clarsimp
   apply(case_tac "fair_seq \<rho> p \<sigma> i", clarsimp)
   apply(rename_tac q s tk)
   apply(subgoal_tac "locally_seq q \<and> jumpfree q")
    apply(frule_tac s=s in available_pos_pstep)
    apply clarify
    apply(subgoal_tac "(SOME x. \<rho> \<turnstile> (q, s) -p\<rightarrow> x) = (q\<lbrakk>p'\<rbrakk>\<^bsub>xs\<^esub>, t)")
     apply(rule_tac x=i in exI, clarsimp)
     apply(rule conjI, clarsimp)
      apply(rule fpos_of_eq, assumption+)
        apply(erule available_rpos)
       apply assumption+
      apply(rule refl)
     apply clarsimp
    apply(rule_tac a="(q\<lbrakk>p'\<rbrakk>\<^bsub>xs\<^esub>, t)" in someI2, assumption)
    apply clarsimp
    apply(drule locally_seq_jumpfree_pstep_unq, assumption, assumption, assumption)
    apply simp
   apply(insert iCOMP_jumpfree[OF fair_seq_iCOMP[where p=p and \<rho>=\<rho>], where j=0, simplified])
   apply(drule_tac x=\<sigma> in meta_spec, clarsimp)
   apply(drule_tac x=i in spec, clarsimp)
   apply(insert iCOMP_jumpfree_locally_seq[OF fair_seq_iCOMP[where p=p and \<rho>=\<rho>], where j=0, simplified])
   apply(drule_tac x=\<sigma> in meta_spec, clarsimp)
   apply(drule_tac x=i in spec, clarsimp)
  apply(clarsimp simp: EnvCond_i_def)
  apply(rule conjI, rule fair_seq_iCOMP)
  apply(clarsimp simp: cstep_cond_def)
  apply(case_tac i, simp+)
  apply(rename_tac n)
  apply(case_tac "fair_seq \<rho> p \<sigma> n", clarsimp split: if_splits)
  done



end


