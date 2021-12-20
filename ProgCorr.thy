(* *********************************************************************

    Theory ProgCorr.thy is part of a framework for modelling,
    verification and transformation of concurrent imperative
    programs. Copyright (c) 2021  M. Bortin

    The framework is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.
    For more details see the license agreement (LICENSE) you should have
    received along with the framework.
    
   ******************************************************************* *)

theory ProgCorr
imports RG
begin
  
    

section "Stepwise correspondence between programs"
  
definition prog_corrC :: "(nat \<Rightarrow> 'a LA) \<Rightarrow> (nat \<Rightarrow> 'b LA) \<Rightarrow> ('a \<times> 'b) set \<Rightarrow> ('a LA \<times> 'b LA) set \<Rightarrow> bool"
  where "prog_corrC \<rho> \<rho>' r X \<equiv> (\<forall>(p, p') \<in> X. \<forall>(s, t) \<in> r. \<forall>p'' t'. \<rho>' \<turnstile> (p', t) -p\<rightarrow> (p'', t') \<longrightarrow> 
                                 (\<exists>s' p'''. \<rho> \<turnstile> (p, s) -p\<rightarrow> (p''', s') \<and> (s', t') \<in> r \<and> (p''', p'') \<in> X)) \<and>
                                 (\<forall>p. (p, Skip) \<in> X \<longrightarrow> p = Skip) \<and>
                                 (\<forall>p. (Skip, p) \<in> X \<longrightarrow> p = Skip)"
  
definition prog_corr :: "(nat \<Rightarrow> 'a LA) \<Rightarrow> (nat \<Rightarrow> 'b LA) \<Rightarrow> ('a \<times> 'b) set \<Rightarrow> ('a LA \<times> 'b LA) set"
  where "prog_corr \<rho> \<rho>' r \<equiv> \<Union>{X. prog_corrC \<rho> \<rho>' r X}"
    
abbreviation prog_corr' :: "(nat \<Rightarrow> 'a LA) \<Rightarrow> (nat \<Rightarrow> 'b LA) \<Rightarrow> 'a LA \<Rightarrow> ('a \<times> 'b) set \<Rightarrow> 'b LA \<Rightarrow> bool" 
   ("_, _ \<Turnstile> _ \<sqsupseteq>\<^bsub>_\<^esub> _" [71, 71, 20, 10, 20] 71)
   where "\<rho>, \<rho>' \<Turnstile> p \<sqsupseteq>\<^bsub>r\<^esub> p' \<equiv> (p, p') \<in> prog_corr \<rho> \<rho>' r"

definition prog_mucorr :: "(nat \<Rightarrow> 'a LA) \<Rightarrow> (nat \<Rightarrow> 'b LA) \<Rightarrow> ('a \<times> 'b) set \<Rightarrow> ('a LA \<times> 'b LA) set"
  where "prog_mucorr \<rho> \<rho>' r = {(p, p') |p p'. (\<rho>, \<rho>' \<Turnstile> p \<sqsupseteq>\<^bsub>r\<^esub> p') \<and> \<rho>', \<rho> \<Turnstile> p' \<sqsupseteq>\<^bsub>r\<inverse>\<^esub> p}" 

abbreviation prog_mucorr' :: "(nat \<Rightarrow> 'a LA) \<Rightarrow> (nat \<Rightarrow> 'b LA) \<Rightarrow> 'a LA \<Rightarrow> ('a \<times> 'b) set \<Rightarrow> 'b LA \<Rightarrow> bool" 
   ("_, _ \<Turnstile> _ \<approx>\<^bsub>_\<^esub> _" [71, 71, 20, 10, 20] 71)
   where "\<rho>, \<rho>' \<Turnstile> p \<approx>\<^bsub>r\<^esub> p' \<equiv> (p, p') \<in> prog_mucorr \<rho> \<rho>' r"

abbreviation prog_mucorr'' :: "(nat \<Rightarrow> 'a LA) \<Rightarrow> 'a LA \<Rightarrow> ('a \<times> 'a) set \<Rightarrow> 'a LA \<Rightarrow> bool" 
   ("_ \<Turnstile> _ \<approx>\<^bsub>_\<^esub> _" [71, 20, 10, 20] 71)
   where "\<rho> \<Turnstile> p \<approx>\<^bsub>r\<^esub> p' \<equiv> (p, p') \<in> prog_mucorr \<rho> \<rho> r"


abbreviation prog_corr'' :: "(nat \<Rightarrow> 'a LA) \<Rightarrow> 'a LA \<Rightarrow> ('a \<times> 'a) set \<Rightarrow> 'a LA \<Rightarrow> bool" 
   ("_ \<Turnstile> _ \<sqsupseteq>\<^bsub>_\<^esub> _" [71, 20, 20, 20] 71)
   where "\<rho> \<Turnstile> p \<sqsupseteq>\<^bsub>r\<^esub> p' \<equiv> (p, p') \<in> prog_corr \<rho> \<rho> r"

abbreviation prog_corr'_id :: "(nat \<Rightarrow> 'a LA) \<Rightarrow> (nat \<Rightarrow> 'a LA) \<Rightarrow> 'a LA \<Rightarrow> 'a LA \<Rightarrow> bool"  
   ("_, _ \<Turnstile> _ \<sqsupseteq> _" [71, 71, 20, 20] 71)
   where "\<rho>, \<rho>' \<Turnstile> p \<sqsupseteq> p' \<equiv> (p, p') \<in> prog_corr \<rho> \<rho>' Id"


abbreviation prog_corr'_id' :: "(nat \<Rightarrow> 'a LA) \<Rightarrow> 'a LA \<Rightarrow> 'a LA \<Rightarrow> bool"  
   ("_ \<Turnstile> _ \<sqsupseteq> _" [71, 20, 20] 71)
   where "\<rho> \<Turnstile> p \<sqsupseteq> p' \<equiv> (p, p') \<in> prog_corr \<rho> \<rho> Id"


abbreviation prog_corr''' :: "'a LA \<Rightarrow> ('a \<times> 'a) set \<Rightarrow> 'a LA \<Rightarrow> bool" 
   ("\<Turnstile> _ \<sqsupseteq>\<^bsub>_\<^esub> _" [20, 20, 20] 71)
   where "\<Turnstile> p \<sqsupseteq>\<^bsub>r\<^esub> p' \<equiv> (p, p') \<in> prog_corr (\<lambda>x. Skip) (\<lambda>x. Skip) r"

abbreviation prog_corr'''_id :: "'a LA \<Rightarrow> 'a LA \<Rightarrow> bool" 
   ("\<Turnstile> _ \<sqsupseteq> _" [20, 20] 71)
   where "\<Turnstile> p \<sqsupseteq> p' \<equiv> (p, p') \<in> prog_corr (\<lambda>x. Skip) (\<lambda>x. Skip) Id"


abbreviation prog_mucorr'_id :: "(nat \<Rightarrow> 'a LA) \<Rightarrow> (nat \<Rightarrow> 'a LA) \<Rightarrow> 'a LA \<Rightarrow> 'a LA \<Rightarrow> bool"  
   ("_, _ \<Turnstile> _ \<approx> _" [71, 71, 20, 20] 71)
   where "\<rho>, \<rho>' \<Turnstile> p \<approx> p' \<equiv> (p, p') \<in> prog_mucorr \<rho> \<rho>' Id"


abbreviation prog_mucorr'_id' :: "(nat \<Rightarrow> 'a LA) \<Rightarrow> 'a LA \<Rightarrow> 'a LA \<Rightarrow> bool"  
   ("_ \<Turnstile> _ \<approx> _" [71, 20, 20] 71)
   where "\<rho> \<Turnstile> p \<approx> p' \<equiv> (p, p') \<in> prog_mucorr \<rho> \<rho> Id"


lemma small_step_eqv :
"(\<rho>, \<rho>' \<Turnstile> p \<approx> p') = ((\<rho>, \<rho>' \<Turnstile> p \<sqsupseteq> p') \<and> (\<rho>', \<rho> \<Turnstile> p' \<sqsupseteq> p))"  
  by(simp add: prog_mucorr_def)



lemma prog_corrC_skipD1 :
"(Skip, p) \<in> X \<Longrightarrow> prog_corrC \<rho> \<rho>' r X \<Longrightarrow> p = Skip"
  by(clarsimp simp: prog_corrC_def)  
    
lemma prog_corrC_skipD2 :
"(p, Skip) \<in> X \<Longrightarrow> prog_corrC \<rho> \<rho>' r X \<Longrightarrow> p = Skip"
  by(clarsimp simp: prog_corrC_def)


lemma prog_corrC_step :
"(p, p') \<in> X \<Longrightarrow> prog_corrC \<rho> \<rho>' r X \<Longrightarrow> (s, t) \<in> r \<Longrightarrow> \<rho>' \<turnstile> (p', t) -p\<rightarrow> (p'', t') \<Longrightarrow> 
   \<exists>s' p'''. \<rho> \<turnstile> (p, s) -p\<rightarrow> (p''', s') \<and> (s', t') \<in> r \<and> (p''', p'') \<in> X"
  apply(simp add: prog_corrC_def)
  apply(drule conjunct1)
  apply(drule bspec, assumption, simp)+
  done

lemma prog_corrC_steps :
"\<rho>' \<turnstile> (p', t) -p\<rightarrow>\<^sup>n (p'', t') \<Longrightarrow> (p, p') \<in> X \<Longrightarrow> prog_corrC \<rho> \<rho>' r X \<Longrightarrow> (s, t) \<in> r \<Longrightarrow> 
   \<exists>s' p'''. \<rho> \<turnstile> (p, s) -p\<rightarrow>\<^sup>n (p''', s') \<and> (s', t') \<in> r \<and> (p''', p'') \<in> X"
  apply(induct n arbitrary: p s p' t p'' t', simp)
  apply clarsimp
  apply((drule meta_spec)+, (drule meta_mp, assumption)+)
  apply clarsimp
  apply(drule_tac p=p''' in prog_corrC_step, assumption, assumption, assumption)
  apply clarify
  apply(rename_tac s1 p1)
  apply(rule_tac x=s1 in exI, simp)
  apply(rule_tac x=p1 in exI, simp)
  apply(erule relcomppI, assumption)
  done


    
lemma prog_corrC_skips :
"prog_corrC \<rho> \<rho>' r {(Skip, Skip)}"    
  apply(clarsimp simp: prog_corrC_def)
  apply(erule Skip_pstep)
  done


lemma prog_corrC_union :
"prog_corrC \<rho> \<rho>' r X \<Longrightarrow> prog_corrC \<rho> \<rho>' r Z \<Longrightarrow> prog_corrC \<rho> \<rho>' r (X \<union> Z)"
  apply(subst prog_corrC_def, simp)
  apply(rule conjI, clarsimp)
   apply(erule disjE)
    apply(drule prog_corrC_step, assumption+)
    apply fastforce
   apply(drule prog_corrC_step, assumption+)
   apply fastforce
  apply(rule conjI, clarsimp)+
    apply(erule prog_corrC_skipD2, assumption)
    apply(clarify, erule prog_corrC_skipD2, assumption)    
  apply clarsimp
  apply(rule conjI, clarify, erule prog_corrC_skipD1, assumption)
  apply(clarify, erule prog_corrC_skipD1, assumption)
  done

    
lemma prog_corrC_Union :
"\<forall>x \<in> S. prog_corrC \<rho> \<rho>' r x \<Longrightarrow> prog_corrC \<rho> \<rho>' r (\<Union>S)"    
  apply(subst prog_corrC_def)
  apply(rule conjI, clarsimp)
   apply(drule bspec, assumption)
   apply(drule prog_corrC_step, assumption+)
   apply fastforce
  apply(rule conjI, clarsimp)
   apply(drule bspec, assumption)
   apply(drule prog_corrC_skipD2, assumption+)
  apply clarsimp
  apply(drule bspec, assumption)
  apply(drule prog_corrC_skipD1, assumption+)    
  done


lemma prog_corrC_comp :
"prog_corrC \<rho> \<rho>' r1 X \<Longrightarrow> prog_corrC \<rho>' \<rho>'' r2 Z \<Longrightarrow>
 prog_corrC \<rho> \<rho>'' (r1 O r2) (X O Z)"
  apply(subst prog_corrC_def, simp)
  apply(rule conjI, clarsimp)
   apply(frule prog_corrC_step, assumption, assumption, assumption)
   apply clarsimp
   apply(drule prog_corrC_step, assumption, assumption, assumption)
   apply clarsimp
   apply(rename_tac t1 p1)
   apply(rule_tac x=t1 in exI)
   apply(rule_tac x=p1 in exI, simp)
   apply(rule conjI)
    apply(erule relcompI, assumption)+
  apply(rule conjI, clarsimp)
   apply(drule prog_corrC_skipD2, assumption)
   apply clarsimp
   apply(drule prog_corrC_skipD2, assumption+)
  apply clarify
  apply(drule prog_corrC_skipD1, assumption)
  apply clarsimp    
  apply(drule prog_corrC_skipD1, assumption+)
  done


lemma prog_corrC_Id :
"prog_corrC \<rho> \<rho> Id Id"
  by(clarsimp simp: prog_corrC_def)


lemma prog_corr_skipD1 :
"\<rho>, \<rho>' \<Turnstile> SKIP \<sqsupseteq>\<^bsub>r\<^esub> p \<Longrightarrow> p = SKIP"
  by(clarsimp simp: prog_corr_def, erule prog_corrC_skipD1, assumption)  
    
lemma prog_corr_skipD2 :
"\<rho>, \<rho>' \<Turnstile> p \<sqsupseteq>\<^bsub>r\<^esub> SKIP \<Longrightarrow> p = SKIP"
  by(clarsimp simp: prog_corr_def, erule prog_corrC_skipD2, assumption)  


lemma prog_corr_step :
"\<rho>, \<rho>' \<Turnstile> p \<sqsupseteq>\<^bsub>r\<^esub> p' \<Longrightarrow> (s, t) \<in> r \<Longrightarrow> \<rho>' \<turnstile> (p', t) -p\<rightarrow> (p'', t') \<Longrightarrow> 
 \<exists>s' p'''. \<rho> \<turnstile> (p, s) -p\<rightarrow> (p''', s') \<and> (s', t') \<in> r \<and> \<rho>, \<rho>' \<Turnstile> p''' \<sqsupseteq>\<^bsub>r\<^esub> p''"
  apply(clarsimp simp: prog_corr_def)
  apply(drule prog_corrC_step, assumption+)
  by fastforce


lemma prog_corr_trans :
"\<rho>, \<rho>' \<Turnstile> p \<sqsupseteq>\<^bsub>r1\<^esub> p' \<Longrightarrow> \<rho>', \<rho>'' \<Turnstile> p' \<sqsupseteq>\<^bsub>r2\<^esub> p'' \<Longrightarrow>
 \<rho>, \<rho>'' \<Turnstile> p \<sqsupseteq>\<^bsub>r1 O r2\<^esub> p''"
  apply(clarsimp simp: prog_corr_def)
  apply(rename_tac X Z)
  apply(rule_tac x="X O Z" in exI)
  apply(rule conjI)
   apply(erule prog_corrC_comp, assumption)
  apply(erule relcompI, assumption)
  done

lemmas prog_corr_trans' = prog_corr_trans[where ?r1.0=Id and ?r2.0=Id, simplified]    
lemmas prog_corr_trans_IdL = prog_corr_trans[where ?r1.0=Id, simplified]
lemmas prog_corr_trans_IdR = prog_corr_trans[where ?r2.0=Id, simplified]


lemma prog_corr_refl :
"\<rho> \<Turnstile> p \<sqsupseteq> p"
  apply(simp add: prog_corr_def)
  apply(rule exI, rule conjI, rule prog_corrC_Id)
  by simp

lemma small_step_eqvD1 :
"\<rho>, \<rho>' \<Turnstile> p \<approx> p' \<Longrightarrow> \<rho>, \<rho>' \<Turnstile> p \<sqsupseteq> p'"
  by(clarsimp simp: small_step_eqv)

lemma small_step_eqvD2 :
"\<rho>, \<rho>' \<Turnstile> p \<approx> p' \<Longrightarrow> \<rho>', \<rho> \<Turnstile> p' \<sqsupseteq> p"
  by(clarsimp simp: small_step_eqv)


lemma small_step_eqv_refl :
"\<rho> \<Turnstile> p \<approx> p"
  apply(clarsimp simp: small_step_eqv)
  by(rule prog_corr_refl)
    
    
lemma small_step_eqv_sym :
"\<rho>, \<rho>' \<Turnstile> p \<approx> p' \<Longrightarrow> \<rho>', \<rho> \<Turnstile> p' \<approx> p"
  by(clarsimp simp: small_step_eqv)
    
lemma small_step_eqv_trans :
"\<rho>, \<rho>' \<Turnstile> p \<approx> p' \<Longrightarrow> \<rho>', \<rho>'' \<Turnstile> p' \<approx> p'' \<Longrightarrow>
 \<rho>, \<rho>'' \<Turnstile> p \<approx> p''"
  apply(clarsimp simp: small_step_eqv)
  apply(drule_tac p''=p'' in prog_corr_trans, assumption)
  apply(drule_tac p=p'' in prog_corr_trans, assumption)    
  by simp




section "Further properties"
    
lemma small_step_eqv_substL :
"\<rho>, \<rho>' \<Turnstile> p \<sqsupseteq>\<^bsub>r\<^esub> p'' \<Longrightarrow> \<rho>, \<rho> \<Turnstile> p \<approx> p' \<Longrightarrow>
 \<rho>, \<rho>' \<Turnstile> p' \<sqsupseteq>\<^bsub>r\<^esub> p''"
  apply(clarsimp simp: small_step_eqv)
  apply(drule_tac p=p' in prog_corr_trans, assumption)
  apply simp
  done
    
lemma small_step_eqv_substR :
"\<rho>, \<rho>' \<Turnstile> p'' \<sqsupseteq>\<^bsub>r\<^esub> p \<Longrightarrow> \<rho>', \<rho>' \<Turnstile> p \<approx> p' \<Longrightarrow>
 \<rho>, \<rho>' \<Turnstile> p'' \<sqsupseteq>\<^bsub>r\<^esub> p'"
  apply(clarsimp simp: small_step_eqv)
  apply(drule_tac p=p'' in prog_corr_trans, assumption)    
  by simp




section "Associativity of sequencing"      
  
lemma prog_corr_seq_assoc1 : 
"\<rho>, \<rho>' \<Turnstile> p \<sqsupseteq>\<^bsub>r\<^esub> p' \<Longrightarrow> \<rho>, \<rho>' \<Turnstile> q \<sqsupseteq>\<^bsub>r\<^esub> q' \<Longrightarrow> \<rho>, \<rho>' \<Turnstile> v \<sqsupseteq>\<^bsub>r\<^esub> v' \<Longrightarrow> 
 \<rho>, \<rho>' \<Turnstile> (p;q);v \<sqsupseteq>\<^bsub>r\<^esub> p';(q';v')"     
  apply(clarsimp simp: prog_corr_def)
  apply(rename_tac P Q V)
  apply(rule_tac x="{(Seq (Seq x q) v, Seq x' (Seq q' v')) | x x'. (x, x') \<in> P} \<union> 
                    {(Seq x v, Seq x' v') | x x'. (x, x') \<in> Q} \<union> V \<union> {(Skip, Skip)}" in exI)
  apply simp
  apply(subst prog_corrC_def)
  apply clarsimp
  apply(rule conjI)
   apply clarsimp
   apply(erule Skip_pstep)
  apply(rule conjI)
   apply clarsimp
   apply(rename_tac s t p'' t')
   apply(erule disjE, clarsimp)
    apply(case_tac "x' = SKIP", clarify)
     apply(drule prog_corrC_skipD2, assumption)
     apply(drule Seq_pstep_Skip, clarsimp)
     apply(rule_tac x=s in exI, simp)
     apply(rule exI, rule conjI)
      apply(rule pstep.Seq, rule pstep.SeqSkip)
     apply fast
    apply(drule Seq_pstep, assumption)
    apply clarsimp
    apply(drule_tac X=P and p=x in prog_corrC_step[rotated -1], assumption+)
    apply clarsimp
    apply(rule_tac x=s' in exI, simp)
    apply(rule exI, rule conjI)
     apply(rule pstep.Seq, erule pstep.Seq)
    apply fast
   apply(erule disjE, clarsimp)
    apply(case_tac "x' = SKIP", clarify)
     apply(drule prog_corrC_skipD2, assumption)
     apply(drule Seq_pstep_Skip, clarsimp)
     apply(rule_tac x=s in exI, simp)
     apply(rule exI, rule conjI)
      apply(rule pstep.SeqSkip)
     apply fast
    apply(drule Seq_pstep, assumption)
    apply clarsimp
    apply(drule_tac X=Q and p=x in prog_corrC_step[rotated -1], assumption+)
    apply clarsimp
    apply(rule_tac x=s' in exI, simp)
    apply(rule exI, rule conjI)
     apply(erule pstep.Seq)
    apply fast
   apply(drule_tac X=V in prog_corrC_step[rotated -1], assumption+)  
   apply fast
  apply(rule conjI, clarsimp)
   apply(erule prog_corrC_skipD2, assumption)
  apply clarsimp
  apply(erule prog_corrC_skipD1, assumption)
  done


lemma prog_corr_seq_assoc2 : 
"\<rho>, \<rho>' \<Turnstile> p \<sqsupseteq>\<^bsub>r\<^esub> p' \<Longrightarrow> \<rho>, \<rho>' \<Turnstile> q \<sqsupseteq>\<^bsub>r\<^esub> q' \<Longrightarrow> \<rho>, \<rho>' \<Turnstile> v \<sqsupseteq>\<^bsub>r\<^esub> v' \<Longrightarrow> 
 \<rho>, \<rho>' \<Turnstile> p;(q;v) \<sqsupseteq>\<^bsub>r\<^esub> (p';q');v'"     
  apply(clarsimp simp: prog_corr_def)
  apply(rename_tac P Q V)
  apply(rule_tac x="{(Seq x (Seq q v), Seq (Seq x' q') v') | x x'. (x, x') \<in> P} \<union> 
                    {(Seq x v, Seq x' v') | x x'. (x, x') \<in> Q} \<union> V \<union> {(Skip, Skip)}" in exI)
  apply simp
  apply(subst prog_corrC_def)
  apply clarsimp
  apply(rule conjI)
   apply clarsimp
   apply(erule Skip_pstep)
  apply(rule conjI)
   apply clarsimp
   apply(rename_tac s t p'' t')
   apply(erule disjE, clarsimp)
    apply(drule Seq_pstep, simp, clarsimp)
    apply(case_tac "x' = SKIP", clarify)
     apply(drule prog_corrC_skipD2, assumption)
     apply(drule Seq_pstep_Skip, clarsimp)
     apply(rule_tac x=s in exI, simp)
     apply(rule exI, rule conjI)
      apply(rule pstep.SeqSkip)
     apply fast
    apply(drule Seq_pstep, simp, clarsimp)
    apply(drule_tac X=P and p=x in prog_corrC_step[rotated -1], assumption+)
    apply clarsimp
    apply(rule_tac x=s' in exI, simp)
    apply(rule exI, rule conjI)
     apply(erule pstep.Seq, fast)
   apply(erule disjE, clarsimp)
    apply(case_tac "x' = SKIP", clarify)
     apply(drule prog_corrC_skipD2, assumption)
     apply(drule Seq_pstep_Skip, clarsimp)
     apply(rule_tac x=s in exI, simp)
     apply(rule exI, rule conjI)
      apply(rule pstep.SeqSkip)
     apply fast
    apply(drule Seq_pstep, assumption)
    apply clarsimp
    apply(drule_tac X=Q and p=x in prog_corrC_step[rotated -1], assumption+)
    apply clarsimp
    apply(rule_tac x=s' in exI, simp)
    apply(rule exI, rule conjI)
     apply(erule pstep.Seq)
    apply fast
   apply(drule_tac X=V in prog_corrC_step[rotated -1], assumption+)  
   apply fast
  apply(rule conjI, clarsimp)
   apply(erule prog_corrC_skipD2, assumption)
  apply clarsimp
  apply(erule prog_corrC_skipD1, assumption)
  done


theorem small_step_eqv_seq_assoc : 
"\<rho> \<Turnstile> (p;q);v \<approx> p;q;v"
  apply(simp add: small_step_eqv)
  apply(rule conjI)
  apply(rule prog_corr_seq_assoc1, (rule prog_corr_refl)+)
  apply(rule prog_corr_seq_assoc2, (rule prog_corr_refl)+)
  done



section "Structural correspondence rules"

lemma prog_corr_skips :
"\<rho>, \<rho>' \<Turnstile> SKIP \<sqsupseteq>\<^bsub>r\<^esub> SKIP"
  apply(simp add: prog_corr_def)
  apply(rule_tac x="{(Skip, Skip)}" in exI, simp)
  by(rule prog_corrC_skips)


lemma prog_corr_basics : 
"(\<And>s t. (s, t) \<in> r \<Longrightarrow> (f s, f' t) \<in> r) \<Longrightarrow>
  \<rho>, \<rho>' \<Turnstile> Basic f \<sqsupseteq>\<^bsub>r\<^esub> Basic f'" 
  apply(simp add: prog_corr_def)
  apply(rule_tac x="{(Basic f, Basic f'), (Skip, Skip)}" in exI, simp add: prog_corrC_def)
  apply(rule conjI, clarsimp)
   apply(drule Basic_pstep, clarsimp)
   apply(drule meta_spec, drule meta_spec, drule meta_mp, assumption)
   apply(rule exI, rule conjI, rule pstep.Basic, assumption)
  apply clarsimp
  by(erule Skip_pstep)




lemma prog_corr_cjumps : 
"\<rho>, \<rho>' \<Turnstile> \<rho> i \<sqsupseteq>\<^bsub>r\<^esub> \<rho>' j \<Longrightarrow> \<rho>, \<rho>' \<Turnstile> p \<sqsupseteq>\<^bsub>r\<^esub> p' \<Longrightarrow>
 \<forall>(s, t) \<in> r. (s \<in> C) = (t \<in> C') \<Longrightarrow> 
  \<rho>, \<rho>' \<Turnstile> CJUMP C TO i OTHERWISE p END \<sqsupseteq>\<^bsub>r\<^esub> CJUMP C' TO j OTHERWISE p' END" 
  apply(simp add: prog_corr_def, clarify)
  apply(rename_tac X Z)
  apply(rule_tac x="{(CJump C i p, CJump C' j p')} \<union> X \<union> Z" in exI, simp)
  apply(subst prog_corrC_def, simp)
  apply(rule conjI, clarsimp)
   apply(drule CJump_pstep, clarify)
   apply(erule disjE, clarsimp)
    apply(rename_tac s t')
    apply(rule_tac x=s in exI)
    apply(rule exI, rule conjI, rule pstep.CJumpT, fast)
    apply simp
   apply clarsimp
   apply(rename_tac s t')
   apply(rule_tac x=s in exI)
   apply(rule exI, rule conjI, rule pstep.CJumpF, fast)
   apply simp
  apply(rule conjI, clarsimp)
   apply(erule disjE)
    apply(drule prog_corrC_step[rotated -1], assumption+)
    apply fast
   apply(drule prog_corrC_step[rotated -1], assumption+)
   apply fast
  apply(rule conjI, clarify)+
    apply(rule prog_corrC_skipD2, assumption+)
   apply(clarify, rule prog_corrC_skipD2, assumption+)
  apply clarify
  apply(rule conjI, clarify)+
   apply(rule prog_corrC_skipD1, assumption+)
  apply(clarify, rule prog_corrC_skipD1, assumption+)
  done





lemma prog_corr_whiles : 
"\<rho>, \<rho>' \<Turnstile> p \<sqsupseteq>\<^bsub>r\<^esub> p' \<Longrightarrow> \<rho>, \<rho>' \<Turnstile> q \<sqsupseteq>\<^bsub>r\<^esub> q' \<Longrightarrow>
 \<forall>(s, t) \<in> r. (s \<in> C) = (t \<in> C') \<Longrightarrow>
  \<rho>, \<rho>' \<Turnstile> WHILE C \<lbrakk>inv: I\<rbrakk> DO p SUBSEQUENTLY q OD \<sqsupseteq>\<^bsub>r\<^esub> 
          WHILE C' \<lbrakk>inv: I'\<rbrakk> DO p' SUBSEQUENTLY q' OD" 
  apply(simp add: prog_corr_def, clarify)
  apply(rename_tac X Z)
  apply(rule_tac x="{(While C I p q, 
                      While C' I' p' q')} \<union>
                    {(SKIP;While C I p q, 
                      SKIP;While C' I' p' q')} \<union>
                    {(u ; (SKIP ; While C I p q), 
                      v ; (SKIP ; While C' I' p' q')) | u v. (u, v) \<in> X} \<union>
                     Z" in exI, simp)
  apply(subst prog_corrC_def, simp)
  apply(rule conjI, clarsimp)
   apply(drule Seq_pstep_Skip, clarify)
  apply(intro exI, rule conjI, rule pstep.SeqSkip, fast)
  apply(rule conjI, clarsimp)
   apply(rename_tac s t p'' t')
   apply(drule While_pstep, clarify)
   apply(erule disjE, clarify)
    apply(rule_tac x=s in exI, simp)
    apply(rule exI, rule conjI, rule pstep.WhileT, fast, fast)
   apply clarsimp
   apply(rule_tac x=s in exI, simp)
   apply(rule exI, rule conjI, rule pstep.WhileF, fast, fast)
  apply(rule conjI, clarsimp)
   apply(erule disjE, clarify)
    apply(case_tac "v=SKIP", clarify)
     apply(drule prog_corrC_skipD2, assumption, clarify)
     apply(drule Seq_pstep_Skip, clarify)
     apply(intro exI, rule conjI, rule pstep.SeqSkip, fast)
    apply(drule Seq_pstep, simp, clarify)
    apply(drule prog_corrC_step[rotated -1], assumption+)
    apply clarsimp
    apply(intro exI, rule conjI, erule pstep.Seq, fast)
   apply(drule prog_corrC_step[rotated -1], assumption+)
   apply fast
  apply(rule conjI, clarify)
   apply(rule prog_corrC_skipD2, assumption+)
  apply(clarify, rule prog_corrC_skipD1, assumption+)
  done


subsection "Program correspondence and the parallel operator"

text "subsuming commutativity property"
theorem prog_corr_parallels : 
"\<forall>i<length ps. \<rho>,\<rho>' \<Turnstile> fst(ps!\<sigma> i) \<sqsupseteq>\<^bsub>r\<^esub> fst(ps'!i) \<Longrightarrow> length ps = length ps' \<Longrightarrow>
 inj_on \<sigma> {0..<length ps'} \<Longrightarrow> \<forall>i<length ps'. \<sigma> i < length ps \<Longrightarrow>
 \<rho>,\<rho>' \<Turnstile> Parallel ps \<sqsupseteq>\<^bsub>r\<^esub> Parallel ps'"  
  apply(clarsimp simp: prog_corr_def)
  apply(subst (asm) Skolem_list_nth)
  apply clarsimp
  apply(rename_tac Xs)
  apply(rule_tac x="{(Parallel u, Parallel v) |u v. length u = length v \<and> length v = length Xs \<and>
                     (\<forall>i<length v. prog_corrC \<rho> \<rho>' r (Xs ! i) \<and> (fst (u ! \<sigma> i), fst (v ! i)) \<in> Xs ! i)}
                    \<union> {(Skip, Skip)}" 
        in exI, simp) 
  apply(subst prog_corrC_def, clarsimp)
  apply(rule conjI, clarsimp)
   apply(erule Skip_pstep)
  apply clarsimp
  apply(rename_tac s t us p'' t' vs) 
  apply(drule Parallel_pstep)
  apply(erule disjE, clarsimp)
   apply(frule_tac x=i in spec, drule mp, assumption, erule conjE)
   apply(drule_tac X="Xs!i" in prog_corrC_step[rotated -1], assumption+)
   apply clarify
   apply(rule_tac x=s' in exI)
  apply(rule exI, rule conjI, erule_tac i="\<sigma> i" in pstep.Parallel, simp, clarsimp)
   apply(rename_tac j)
   apply(case_tac "j = i", clarsimp)
   apply(subgoal_tac "\<sigma> j \<noteq> \<sigma> i")
    apply clarsimp
   apply clarify
   apply(erule notE, erule inj_onD, assumption, simp, simp)
  apply clarsimp
  apply(rule_tac x=s in exI, rule conjI, rule pstep.ParallelSkip)
  apply clarsimp
   apply(drule mem_nth, clarsimp)
   apply(frule_tac inj_on_surj_set_intv, assumption)
   apply(drule_tac x=i in spec, drule mp, assumption, erule exE)
   apply(rename_tac j, clarify)
   apply(drule_tac x=j in spec, drule mp, assumption, erule conjE)
   apply(drule prog_corrC_skipD2, assumption)
   apply(drule_tac f=fst in arg_cong, simp)
  by assumption


lemma prog_corr_parallels' :
"(\<And>i. i < length ps \<Longrightarrow> \<rho>, \<rho>' \<Turnstile> fst (ps ! i) \<sqsupseteq>\<^bsub>r\<^esub> fst (ps' ! i)) \<Longrightarrow>
 length ps = length ps' \<Longrightarrow>
  \<rho>, \<rho>' \<Turnstile> Parallel ps \<sqsupseteq>\<^bsub>r\<^esub> Parallel ps'"
  apply(rule prog_corr_parallels[where \<sigma>=id, simplified, rule_format])
  by(fast, assumption, simp)


lemma prog_corr_scheme :
"(\<And>i. n \<le> i \<Longrightarrow> i < m \<Longrightarrow> \<rho>, \<rho>' \<Turnstile> fst (f i) \<sqsupseteq>\<^bsub>r\<^esub> fst (g i)) \<Longrightarrow>
  \<rho>, \<rho>' \<Turnstile> Parallel (map f [n..<m]) \<sqsupseteq>\<^bsub>r\<^esub> Parallel (map g [n..<m])"
  apply(rule prog_corr_parallels')
  by simp+


lemma prog_corr_parallel_app :
"\<rho>, \<rho>' \<Turnstile> Parallel as \<sqsupseteq>\<^bsub>r\<^esub> Parallel as' \<Longrightarrow>
 \<rho>, \<rho>' \<Turnstile> Parallel bs \<sqsupseteq>\<^bsub>r\<^esub> Parallel bs' \<Longrightarrow>
 length as = length as' \<Longrightarrow>
 length bs = length bs' \<Longrightarrow>
 \<rho>, \<rho>' \<Turnstile> Parallel (as@bs) \<sqsupseteq>\<^bsub>r\<^esub> Parallel (as'@bs')"
  apply(simp add: prog_corr_def, clarify)
  apply(rename_tac A B)
  apply(rule_tac x="{(Parallel (xs@zs), Parallel (xs'@zs')) | xs zs xs' zs'. 
                       (Parallel xs, Parallel xs') \<in> A \<and> length xs = length xs' \<and>
                       (Parallel zs, Parallel zs') \<in> B \<and> length zs = length zs'}
                    \<union> {(Skip, Skip)}" in exI, simp)
  apply(subst prog_corrC_def, clarsimp)
  apply(rule conjI, clarsimp)
   apply(erule Skip_pstep)
  apply(rule conjI, clarsimp)
   apply(drule Parallel_pstep)
   apply(erule disjE, clarsimp)
    apply(case_tac "i < length xs'")
     apply(subst (asm) nth_append, simp)
     apply(frule_tac p'="Parallel xs'" and X=A in prog_corrC_step[rotated 1], assumption)
       apply(erule pstep.Parallel, assumption+)
     apply clarsimp
     apply(drule Parallel_pstep)
     apply(erule disjE, clarsimp)
      apply(rename_tac j p'')
      apply(intro exI, rule conjI, rule_tac i=j in pstep.Parallel)
        apply(subst nth_append, simp)
       apply simp
      apply(subst list_update_append, simp)+
      apply(subst nth_append, simp)+
      apply(intro exI, rule conjI, rule refl)+
      apply simp
     apply clarsimp
     apply(drule_tac X=A in prog_corrC_skipD1, assumption)
     apply clarify
    apply(drule leI)
    apply(subst (asm) nth_append, simp)
    apply(frule_tac p'="Parallel zs'" and X=B in prog_corrC_step[rotated 1], assumption)
      apply(erule pstep.Parallel, simp, assumption+)
    apply clarsimp
    apply(drule Parallel_pstep)
    apply(erule disjE, clarsimp)
     apply(rename_tac j p'')
     apply(intro exI, rule conjI, rule_tac i="j+length xs" in pstep.Parallel)
       apply(subst nth_append, simp)
      apply simp
     apply(subst list_update_append, simp)+
     apply(subst nth_append, simp)+
     apply(intro exI, rule conjI, rule refl)+
     apply simp
    apply clarsimp
    apply(drule_tac X=B in prog_corrC_skipD1, assumption)
    apply clarify
   apply clarsimp
   apply(rule exI, rule conjI)
    apply(rule pstep.ParallelSkip)
    apply(frule_tac p="Parallel xs" in prog_corrC_step, assumption+)
     apply(rule pstep.ParallelSkip, clarsimp)
    apply clarsimp
    apply(drule_tac X=A in prog_corrC_skipD2, assumption)
    apply clarify
    apply(drule Parallel_pstep_to_Skip)
    apply(frule_tac p="Parallel zs" in prog_corrC_step, assumption+)
     apply(rule pstep.ParallelSkip, clarsimp)
    apply clarsimp
    apply(drule_tac X=B in prog_corrC_skipD2, assumption)
    apply clarify
    apply(drule Parallel_pstep_to_Skip)
    apply fastforce
   apply assumption
  apply(intro exI, rule conjI, rule refl)+
  by simp




lemma prog_corr_parallel_Cons :
"\<rho>, \<rho>' \<Turnstile> Parallel ps \<sqsupseteq>\<^bsub>r\<^esub> Parallel ps' \<Longrightarrow>
 \<rho>, \<rho>' \<Turnstile> p \<sqsupseteq>\<^bsub>r\<^esub> p' \<Longrightarrow>
 length ps = length ps' \<Longrightarrow>
 \<rho>, \<rho>' \<Turnstile> Parallel ((p, a)#ps) \<sqsupseteq>\<^bsub>r\<^esub> Parallel ((p', a')#ps')"
  apply(drule_tac as="[(p,a)]" and as'="[(p',a')]" in prog_corr_parallel_app[rotated 1])
     apply(simp, assumption)
   apply(rule prog_corr_parallels', simp)
  by simp+






subsection "Further rules"

lemma prog_corr_seqs : 
"\<rho>, \<rho>' \<Turnstile> p \<sqsupseteq>\<^bsub>r\<^esub> p' \<Longrightarrow> \<rho>, \<rho>' \<Turnstile> q \<sqsupseteq>\<^bsub>r\<^esub> q' \<Longrightarrow> 
 \<rho>, \<rho>' \<Turnstile> (p;q) \<sqsupseteq>\<^bsub>r\<^esub> (p';q')"
  apply(clarsimp simp: prog_corr_def)
  apply(rename_tac X Z)
  apply(rule_tac x="{(Seq u q, Seq v q') | u v. (u, v) \<in> X} \<union> Z" in exI, simp) 
  apply(subst prog_corrC_def, simp)
  apply(rule conjI, clarsimp)
   apply(erule disjE, clarsimp)
  apply(case_tac "v=Skip", clarify)
     apply(drule prog_corrC_skipD2, assumption)
     apply clarify
     apply(drule Seq_pstep_Skip, clarsimp)
     apply(intro exI, rule conjI, rule pstep.SeqSkip)
     apply fast
    apply(drule Seq_pstep, assumption)
    apply clarsimp
    apply(drule_tac p'=v in prog_corrC_step, assumption+)
    apply clarify
    apply(intro exI, rule conjI, erule pstep.Seq)
    apply fast
   apply(drule_tac X=Z in prog_corrC_step[rotated 2], assumption+)
   apply fast
  apply(rule conjI, clarsimp)
   apply(erule prog_corrC_skipD2, assumption)
  apply clarify
  apply(erule prog_corrC_skipD1, assumption)
  done


lemma prog_corr_conds : 
"\<rho>, \<rho>' \<Turnstile> p \<sqsupseteq>\<^bsub>r\<^esub> p' \<Longrightarrow> \<rho>, \<rho>' \<Turnstile> q \<sqsupseteq>\<^bsub>r\<^esub> q' \<Longrightarrow> 
 \<forall>(s, t) \<in> r. (s \<in> C) = (t \<in> C') \<Longrightarrow>
 \<rho>, \<rho>' \<Turnstile> (IF C THEN p ELSE q FI) \<sqsupseteq>\<^bsub>r\<^esub> 
           IF C' THEN p' ELSE q' FI"
  apply(clarsimp simp: prog_corr_def)
  apply(rename_tac X Z)
  apply(rule_tac x="{(Cond C p q, Cond C' p' q')} \<union> X \<union> Z" in exI, simp) 
  apply(subst prog_corrC_def, simp)
  apply(rule conjI, clarsimp)
   apply(drule Cond_pstep, clarify)
   apply(erule disjE, clarsimp)
    apply(rename_tac s t)
    apply(rule_tac x=s in exI)
    apply(rule exI, rule conjI, rule pstep.CondT, fast, fast)
   apply clarsimp
   apply(rename_tac s t)
   apply(rule_tac x=s in exI)
   apply(rule exI, rule conjI, rule pstep.CondF, fast, fast)
  apply(rule conjI, clarsimp)
   apply(erule disjE)
    apply(drule_tac X=X in prog_corrC_step[rotated 2], assumption+)
    apply fast
   apply(drule_tac X=Z in prog_corrC_step[rotated 2], assumption+)
   apply fast
  apply(rule conjI, clarsimp)+
    apply(erule prog_corrC_skipD2, assumption)
   apply clarify
   apply(erule prog_corrC_skipD2, assumption)
  apply(rule allI, rule conjI)
   apply clarify
   apply(erule prog_corrC_skipD1, assumption)
  apply clarify
  apply(erule prog_corrC_skipD1, assumption)
  done


lemma prog_corr_awaits : 
"\<rho>, \<rho>' \<Turnstile> p \<sqsupseteq>\<^bsub>r\<^esub> p' \<Longrightarrow>  
 \<forall>(s, t) \<in> r. t \<in> C' \<longrightarrow> s \<in> C \<Longrightarrow>
 \<rho>, \<rho>' \<Turnstile> (AWAIT C \<lbrakk>ann: a\<rbrakk> THEN p END) \<sqsupseteq>\<^bsub>r\<^esub> AWAIT C' \<lbrakk>ann: a'\<rbrakk> THEN p' END"
  apply(clarsimp simp: prog_corr_def)
  apply(rename_tac X)
  apply(rule_tac x="{(Await C a p, Await C' a' p')} \<union> X" in exI, simp)
  apply(subst prog_corrC_def, simp)
  apply(rule conjI, clarsimp)
   apply(drule Await_pstep, clarify)
   apply(subst (asm) rtranclp_power, clarify)
   apply(drule prog_corrC_steps[rotated 1], assumption+)
   apply clarify
   apply(frule prog_corrC_skipD2, assumption)
   apply clarify
   apply(drule rtranclp_power[THEN iffD2, OF exI])+
   apply(intro exI, rule conjI, rule pstep.Await, fast, assumption)
   apply simp
  apply(rule conjI, clarsimp)
   apply(drule_tac X=X in prog_corrC_step[rotated 2], assumption+)
   apply fast
  apply(rule conjI, clarsimp)
   apply(erule prog_corrC_skipD2, assumption)
  apply clarify
  apply(erule prog_corrC_skipD1, assumption)
  done


lemma prog_corr_await_basic : 
"\<forall>(s, t) \<in> r. s \<in> C \<and> (\<exists>s'. \<rho> \<turnstile> (p, s) -p\<rightarrow>\<^sup>* (SKIP, s') \<and> (s', f t) \<in> r) \<Longrightarrow>
 \<rho>, \<rho>' \<Turnstile> (AWAIT C \<lbrakk>ann: a\<rbrakk> THEN p END) \<sqsupseteq>\<^bsub>r\<^esub> Basic f"
  apply(clarsimp simp: prog_corr_def)
  apply(rule_tac x="{(Await C a p, Basic f), (SKIP, SKIP)}" in exI, simp)
  apply(simp add: prog_corrC_def)
  apply(rule conjI, clarsimp)
   apply(drule Basic_pstep, clarify)
   apply(drule bspec, assumption)
   apply clarsimp
   apply(rule exI, rule conjI, erule pstep.Await, assumption+)
  apply clarsimp
  apply(erule Skip_pstep)
  done


corollary prog_corr_atomic2_basic :
"\<forall>(s, t) \<in> r. (h(g s), f t) \<in> r \<Longrightarrow>
 \<rho>, \<rho>' \<Turnstile> (AWAIT UNIV \<lbrakk>ann: a\<rbrakk> THEN Basic g; Basic h END) \<sqsupseteq>\<^bsub>r\<^esub> Basic f"
  apply(rule prog_corr_await_basic, clarsimp)
  apply(drule bspec, assumption, clarsimp)
  apply(rule exI, rule conjI)
    apply(rule rtranclp_trans)
     apply(rule r_into_rtranclp)
     apply(rule pstep.Seq)
     apply(rule pstep.Basic)
    apply(rule rtranclp_trans)
     apply(rule r_into_rtranclp)
     apply(rule pstep.SeqSkip)
    apply(rule r_into_rtranclp)
   apply(rule pstep.Basic)
  by simp


corollary prog_corr_atomic3_basic :
"\<forall>(s, t) \<in> r. (g3(g2(g1 s)), f t) \<in> r \<Longrightarrow>
 \<rho>, \<rho>' \<Turnstile> (AWAIT UNIV \<lbrakk>ann: a\<rbrakk> THEN Basic g1; Basic g2; Basic g3 END) \<sqsupseteq>\<^bsub>r\<^esub> Basic f"
  apply(rule prog_corr_await_basic, clarsimp)
  apply(drule bspec, assumption, clarsimp)
  apply(rule exI, rule conjI)
   apply(rule rtranclp_trans)
    apply(rule rtranclp_trans)
     apply(rule r_into_rtranclp)
     apply(rule pstep.Seq)
     apply(rule pstep.Basic)
    apply(rule r_into_rtranclp)
    apply(rule pstep.SeqSkip)
   apply(rule rtranclp_trans)
    apply(rule rtranclp_trans)
     apply(rule r_into_rtranclp)
     apply(rule pstep.Seq)
     apply(rule pstep.Basic)
    apply(rule r_into_rtranclp)
    apply(rule pstep.SeqSkip)
   apply(rule r_into_rtranclp)
   apply(rule pstep.Basic)
  by assumption



lemma prog_corr_basic_await : 
"\<forall>(s, t) \<in> r. \<forall>t'. t \<in> C \<longrightarrow> \<rho>' \<turnstile> (p, t) -p\<rightarrow>\<^sup>* (SKIP, t') \<longrightarrow> (f s, t') \<in> r \<Longrightarrow>
 \<rho>, \<rho>' \<Turnstile> Basic f \<sqsupseteq>\<^bsub>r\<^esub> (AWAIT C \<lbrakk>ann: a\<rbrakk> THEN p END)"
  apply(clarsimp simp: prog_corr_def)
  apply(rule_tac x="{(Basic f, Await C a p), (SKIP, SKIP)}" in exI, simp)
  apply(simp add: prog_corrC_def)
  apply(rule conjI, clarsimp)
   apply(drule bspec, assumption)
   apply clarsimp
   apply(drule Await_pstep, clarsimp)
   apply(drule spec, drule mp, assumption)
   apply(rule exI, rule conjI, rule pstep.Basic)
   apply assumption
  apply clarify
  by(erule Skip_pstep)

lemmas prog_corr_basic_atomic = prog_corr_basic_await[where C=UNIV, simplified]




section "Replacement rules for the seq-normalisation"

lemma prog_corr_seqN_cond1 :
"\<rho> \<Turnstile> IF C THEN p ELSE q FI; r \<sqsupseteq> 
      IF C THEN p;r ELSE q;r FI"
  apply(simp add: prog_corr_def)
  apply(rule_tac x="{(Seq (Cond C p q) r, Cond C (Seq p r) (Seq q r))} \<union> Id" in exI, simp)
  apply(simp (no_asm) add: prog_corrC_def)
  apply(rule conjI, clarsimp)
   apply(drule Cond_pstep, clarify)
   apply(erule disjE, clarify)
    apply(rule exI, rule conjI, rule pstep.Seq, erule pstep.CondT, simp)
   apply clarify
    apply(rule exI, rule conjI, rule pstep.Seq, erule pstep.CondF, simp)
  apply fast
  done

lemma prog_corr_seqN_cond2 :
"\<rho> \<Turnstile> IF C THEN p;r ELSE q;r FI \<sqsupseteq> 
      (IF C THEN p ELSE q FI; r)"
  apply(simp add: prog_corr_def)
  apply(rule_tac x="{(Cond C (Seq p r) (Seq q r), Seq (Cond C p q) r)} \<union> Id" in exI, simp)
  apply(simp (no_asm) add: prog_corrC_def)
  apply(rule conjI, clarsimp)
   apply(drule Seq_pstep, simp, clarsimp)
   apply(drule Cond_pstep, clarify)
   apply(erule disjE, clarify)
    apply(rule exI, rule conjI, erule pstep.CondT, simp)
   apply clarify
    apply(rule exI, rule conjI, erule pstep.CondF, simp)
  apply fast
  done

corollary eqv_seqN_cond :
"\<rho> \<Turnstile> IF C THEN p ELSE q FI; r \<approx> IF C THEN p;r ELSE q;r FI"
  by(simp add: small_step_eqv, rule conjI, rule prog_corr_seqN_cond1, 
     rule prog_corr_seqN_cond2)



lemma prog_corr_seqN_while1 :
"\<rho> \<Turnstile> WHILE C \<lbrakk>inv: I\<rbrakk> DO p SUBSEQUENTLY q OD; r \<sqsupseteq> 
      WHILE C \<lbrakk>inv: I'\<rbrakk> DO p SUBSEQUENTLY q;r OD"
  apply(simp add: prog_corr_def)
  apply(rule_tac x="{(Seq (While C I p q) r, While C I' p (Seq q r)),
                     (Seq (Seq Skip (While C I p q)) r, 
                      Seq Skip (While C I' p (Seq q r)))} \<union>
                     {(Seq (Seq u (Seq Skip (While C I p q))) r, 
                       Seq u (Seq Skip (While C I' p (Seq q r)))) |u. u \<in> UNIV} \<union> Id" in exI, simp)
  apply(simp (no_asm) add: prog_corrC_def)
  apply(rule conjI, clarsimp)
   apply(drule While_pstep, clarify)
   apply(erule disjE, clarsimp)
    apply(rule exI, rule conjI)
    apply(rule pstep.Seq, erule pstep.WhileT)
    apply clarsimp
   apply clarsimp
   apply(rule pstep.Seq, erule pstep.WhileF)
  apply clarsimp
  apply(rule conjI, clarsimp)
   apply(drule Seq_pstep_Skip)
   apply clarsimp
   apply(rule exI, rule conjI, rule pstep.Seq, rule pstep.SeqSkip)
   apply clarsimp+
  apply(erule disjE, clarsimp)
   apply(case_tac "u = Skip", clarsimp)
    apply(drule Seq_pstep_Skip)
    apply clarsimp
    apply(rule exI, rule conjI, rule pstep.Seq, rule pstep.SeqSkip)
    apply clarsimp
   apply(drule Seq_pstep, assumption)
   apply clarsimp
   apply(rule exI, rule conjI, rule pstep.Seq, erule pstep.Seq)
   apply clarsimp
  apply fastforce
  done



lemma prog_corr_seqN_while2 :
"\<rho> \<Turnstile> WHILE C \<lbrakk>inv: I\<rbrakk> DO p SUBSEQUENTLY q;r OD \<sqsupseteq> 
      WHILE C \<lbrakk>inv: I'\<rbrakk> DO p SUBSEQUENTLY q OD; r "
  apply(simp add: prog_corr_def)
  apply(rule_tac x="{(While C I p (Seq q r), Seq (While C I' p q) r),
                     (Seq Skip (While C I p (Seq q r)), 
                      Seq (Seq Skip (While C I' p q)) r)} \<union>
                     {(Seq u (Seq Skip (While C I p (Seq q r))), 
                       Seq (Seq u (Seq Skip (While C I' p q))) r) |u. u \<in> UNIV} \<union> Id" in exI, simp)
  apply(simp (no_asm) add: prog_corrC_def)
  apply(rule conjI, clarsimp)
   apply(drule Seq_pstep, simp)
   apply clarsimp
   apply(drule While_pstep, clarify)
   apply(erule disjE, clarsimp)
    apply(rule exI, rule conjI, erule pstep.WhileT)
    apply clarsimp+
   apply(erule pstep.WhileF)
   apply simp
  apply(rule conjI, clarsimp)
   apply(drule Seq_pstep, simp)
   apply clarify
   apply(drule Seq_pstep_Skip, simp)
   apply(rule exI, rule conjI, rule pstep.SeqSkip)
   apply simp
  apply clarsimp
  apply(erule disjE, clarsimp)
   apply(drule Seq_pstep, simp)
   apply clarify
   apply(case_tac "u = Skip", clarify)
    apply(drule Seq_pstep_Skip, simp)
    apply(rule exI, rule conjI, rule pstep.SeqSkip)
    apply simp
   apply(drule Seq_pstep, simp)
   apply clarify
   apply(rule exI, rule conjI, erule pstep.Seq)
   apply clarsimp
  apply fast
  done


corollary eqv_seqN_while :
"\<rho> \<Turnstile> WHILE C \<lbrakk>inv: I\<rbrakk> DO p SUBSEQUENTLY q OD; r \<approx> 
      WHILE C \<lbrakk>inv: I'\<rbrakk> DO p SUBSEQUENTLY q;r OD "
  by(simp add: small_step_eqv, rule conjI, rule prog_corr_seqN_while1, 
     rule prog_corr_seqN_while2)



section "if-normalisation"

lemma prog_corr_condN1 :
"\<rho> j = q \<Longrightarrow>
 \<rho> \<Turnstile> IF C THEN p ELSE q FI \<sqsupseteq> 
          CJUMP -C TO j OTHERWISE p END"
  apply(clarsimp simp:prog_corr_def)
  apply(rule_tac x="{(IF C THEN p ELSE q FI, CJUMP -C TO j OTHERWISE p END)} \<union> Id" in exI, simp)
  apply(simp (no_asm) add: prog_corrC_def)
  apply(rule conjI, clarsimp)
   apply(drule CJump_pstep, clarify)
   apply(erule disjE, clarsimp)
    apply(rule exI, rule conjI, erule pstep.CondF, simp)
   apply clarsimp
   apply(erule pstep.CondT, simp)
  apply clarsimp
  apply(rule_tac x=p'' in exI, simp)
  done


lemma prog_corr_condN2 :
"\<rho> j = q \<Longrightarrow>
 \<rho> \<Turnstile> CJUMP -C TO j OTHERWISE p END \<sqsupseteq> IF C THEN p ELSE q FI"
  apply(clarsimp simp:prog_corr_def)
  apply(rule_tac x="{(CJUMP -C TO j OTHERWISE p END, IF C THEN p ELSE q FI)} \<union> Id" in exI, simp)
  apply(simp (no_asm) add: prog_corrC_def)
  apply(rule conjI, clarsimp)
   apply(drule Cond_pstep, clarify)
   apply(erule disjE, clarsimp)
    apply(rule pstep.CJumpF, simp, simp)
   apply(rule pstep.CJumpT, simp, simp)
  apply clarsimp
  apply fast
  done
 

corollary eqv_condN :
"\<rho> j = q \<Longrightarrow>
 \<rho> \<Turnstile> IF C THEN p ELSE q FI \<approx> CJUMP -C TO j OTHERWISE p END"
  apply(clarsimp simp: small_step_eqv)
  apply(rule conjI)
   apply(rule prog_corr_condN1, rule refl)
  apply(rule prog_corr_condN2, rule refl)
  done


section "while-normalisation"


lemma eqv_while_cjump :
"\<rho> j = CJUMP -C TO i OTHERWISE p;JUMP j END \<Longrightarrow>
 \<rho> i = q \<Longrightarrow> 
 \<rho> \<Turnstile> WHILE C \<lbrakk>inv: I\<rbrakk> DO p SUBSEQUENTLY q OD \<approx> 
         CJUMP -C TO i OTHERWISE p;JUMP j END" 
  apply(clarsimp simp: small_step_eqv)
  apply(rule conjI)
   apply(subst prog_corr_def)
   apply clarsimp
   apply(rule_tac x="{(While C I p (\<rho> i), CJump (-C) i (Seq p (Jump j))),
                     (Seq Skip (While C I p q), Jump j)} \<union>
          {(Seq u (Seq Skip (While C I p q)), Seq u (Jump j)) |u. u \<in> UNIV} \<union> Id" 
     in exI)
   apply(simp add: prog_corrC_def)
   apply(rule conjI, clarsimp)
    apply(drule CJump_pstep, clarsimp)
    apply(erule disjE, clarsimp)
     apply(rule_tac x="\<rho> i" in exI, simp)
     apply(erule pstep.WhileF)
    apply clarsimp
    apply(rule exI, rule conjI, erule pstep.WhileT, simp)
   apply(rule conjI, clarsimp)
    apply(drule Jump_pstep, clarsimp)
    apply(rule exI, rule conjI, rule pstep.SeqSkip, simp)
   apply(rule conjI, clarsimp)
    apply(erule disjE, clarsimp)
     apply(case_tac "u = Skip", clarify)
      apply(drule Seq_pstep_Skip, clarsimp)
      apply(rule exI, rule conjI, rule pstep.SeqSkip, simp)
     apply(drule Seq_pstep, assumption, clarsimp)
     apply(rule exI, rule conjI, erule pstep.Seq, simp)
    apply fast
   apply(clarsimp simp: Jump_def)
  apply(subst prog_corr_def)
  apply clarsimp
   apply(rule_tac x="{(CJump (-C) i (Seq p (Jump j)), While C I p (\<rho> i)),
                     (Jump j, Seq Skip (While C I p q))} \<union>
          {(Seq u (Jump j), Seq u (Seq Skip (While C I p q))) |u. u \<in> UNIV} \<union> Id" 
     in exI)
  apply(simp add: prog_corrC_def)
  apply(rule conjI, clarsimp)
   apply(drule While_pstep, clarsimp)
   apply(erule disjE, clarsimp)
    apply(rule exI, rule conjI, rule pstep.CJumpF, simp, simp)
   apply clarsimp
   apply(rule pstep.CJumpT, simp, simp)
  apply(rule conjI, clarsimp)
   apply(drule Seq_pstep_Skip, clarsimp)
   apply(subst Jump_def)
   apply(rule exI, rule conjI, rule pstep.CJumpT, simp, simp)
  apply(rule conjI, clarsimp)
   apply(erule disjE, clarsimp)
    apply(case_tac "u = Skip", clarify)
     apply(drule Seq_pstep_Skip, clarsimp)
     apply(rule exI, rule conjI, rule pstep.SeqSkip, simp)
    apply(drule Seq_pstep, assumption, clarsimp)
    apply(rule exI, rule conjI, erule pstep.Seq, simp)
   apply fast
  apply(clarsimp simp: Jump_def)
  done



section "Program correspondence and R/G properties"


theorem prog_corr_sq_replay :
"\<rho>, \<rho>' \<Turnstile> p \<sqsupseteq>\<^bsub>r\<^esub> p' \<Longrightarrow> 
 sq \<in> EnvCond \<rho>' R' \<Longrightarrow> 
 r O R' \<subseteq> R O r \<Longrightarrow>
 sq!0 = ((p', t), tk) \<Longrightarrow>
 (s, t) \<in> r \<Longrightarrow> 
 \<exists>sq'\<in>EnvCond \<rho> R. sq'!0 = ((p, s), tk) \<and> 
      length sq = length sq' \<and>
   (\<forall>i<length sq. (\<rho>, \<rho>' \<Turnstile> progOf(sq'!i) \<sqsupseteq>\<^bsub>r\<^esub> progOf(sq!i)) \<and>
                  (stateOf(sq'!i), stateOf(sq!i)) \<in> r \<and>
                  tkOf(sq'!i) = tkOf(sq!i))"
  apply(subgoal_tac "sq \<in> COMP \<rho>'")  
   prefer 2
   apply(simp add: EnvCond_def pcs_def)  
  apply(induct sq rule: rev_induct)
   apply(drule COMP_noNil, clarify)
  apply(rename_tac a sq)
  apply(case_tac "sq = []")
   apply clarsimp
   apply(rule_tac x="[((p, s), tk)]" in bexI, simp)
   apply(simp add: EnvCond_def)
   apply(rule_tac x=p in exI, simp add: pcs_def)
   apply(simp (no_asm) add: COMP_eq)
  apply clarsimp
  apply(rename_tac p1 t1 tk1 sq)
  apply(subst (asm) nth_append, simp)
  apply(drule meta_mp)
   apply(erule EnvCond_prefix_cls, simp (no_asm) add: prefix_def, assumption, rule subset_refl)
  apply(drule meta_mp, erule COMP_prefix_cls, simp (no_asm) add: prefix_def, assumption)
  apply clarsimp
  apply(frule_tac x="length sq' - 1" in spec, drule mp, rule pred_less, simp, clarsimp)
  apply(case_tac "sq!(length sq' - 1)", clarsimp)
  apply(rename_tac p0 t0)
  apply(case_tac "sq'!(length sq' - 1)", clarsimp)
  apply(rename_tac p0' t0' tk0')
  apply(case_tac tk1, simp)
   apply(frule_tac i="length sq" in COMP_nth, simp, clarsimp)
   apply(subst (asm) nth_append, simp)+
   apply(simp split: if_splits)
    apply(drule stepR_D1)
    apply(drule prog_corr_step[rotated -1], assumption+)
    apply clarify
    apply(rule_tac x="sq' @ [((p''', s'), True)]" in bexI, simp)
     apply(rule conjI)
      apply(subst nth_append, clarsimp)
     apply clarsimp
     apply(subst nth_append, simp)
     apply(rule conjI, clarify)
      apply(subst nth_append, simp)+
    apply(subst EnvCond_def, simp)
    apply(rule conjI)
     apply(rule_tac x=p in exI)
     apply(simp add: pcs_def)
     apply(rule conjI)
      apply(rule COMP_compose2)
       apply(simp add: EnvCond_def pcs_def)
      apply(subst last_conv_nth, clarsimp)
      apply(simp (no_asm) add: COMP_eq)
      apply(clarsimp simp: stepR_def)
      apply(rule_tac x=True in exI, simp)
     apply(subst hd_conv_nth, simp)
     apply(subst nth_append, clarsimp)
    apply(clarsimp simp: cstep_cond_def)
    apply(case_tac "i = length sq'", clarsimp)
    apply(subst (asm) nth_append, simp)+
    apply(subst (asm) nth_append, simp split: if_splits)
    apply(erule_tac i=i in EnvCond_D, simp, assumption, erule sym, assumption)
   apply(erule notE, rule pred_less[simplified], clarsimp)
  apply clarsimp
  apply(drule_tac i="length sq" and c=p0 and s=t0 and tk=tk0' in EnvCond_D, simp, clarsimp)
    apply(subst nth_append, simp)
    apply(clarify, erule notE, rule pred_less[simplified], clarsimp)
   apply(subst nth_append, simp)
  apply(drule_tac c="(t0', t1)" in subsetD)
   apply(erule relcompI, assumption)
  apply clarsimp
  apply(rename_tac t0' t1' t1)
  apply(rule_tac x="sq' @ [((p0', t1'), False)]" in bexI, simp)
   apply(rule conjI)
    apply(subst nth_append, clarsimp)+
    apply(drule_tac i="length sq" in COMP_nth, simp, simp, clarsimp)
   apply clarsimp
   apply(subst (asm) nth_append, simp split: if_splits)+
    apply(drule stepR_D2, clarify)
   apply(clarify, erule notE, rule pred_less[simplified], clarsimp)
  apply(subst EnvCond_def, simp)
  apply(rule conjI, rule_tac x=p in exI)
   apply(simp add: pcs_def)
   apply(subst hd_conv_nth, clarsimp)
   apply(rule conjI)
     apply(rule COMP_compose2, simp add: EnvCond_def pcs_def)
    apply(subst last_conv_nth, clarsimp)
    apply(simp (no_asm) add: COMP_eq)
    apply(clarsimp simp: stepR_def)
    apply(rule_tac x="False" in exI, simp)
   apply(subst nth_append, clarsimp)
  apply clarify
  apply(case_tac "i=length sq", clarsimp)
   apply(subst nth_append, simp)+
   apply(simp add: cstep_cond_def)
  apply(subst nth_append, simp)+
  apply(rule conjI, clarsimp simp: cstep_cond_def)
   apply(erule_tac i=i in EnvCond_D, simp, assumption, erule sym, assumption)
  apply(clarify, erule notE, rule less_trans, rule pred_less[simplified], clarsimp)
  by simp
 


corollary prog_corr_sq_replayId :
"\<rho>, \<rho>' \<Turnstile> p \<sqsupseteq> p' \<Longrightarrow> 
 sq \<in> COMP \<rho>' \<Longrightarrow> 
 sq!0 = ((p', s), tk) \<Longrightarrow>
 \<exists>sq' \<in> COMP \<rho>. \<exists>tk'. sq'!0 = ((p, s), tk') \<and> 
      length sq = length sq' \<and>
   (\<forall>i<length sq. (\<rho>, \<rho>' \<Turnstile> progOf(sq'!i) \<sqsupseteq> progOf(sq!i)) \<and>
                  stateOf(sq'!i) = stateOf(sq!i) \<and>
                  tkOf(sq'!i) = tkOf(sq!i))"
  apply(drule_tac sq=sq and R'=UNIV and R=UNIV in prog_corr_sq_replay)
      apply(clarsimp simp: EnvCond_def pcs_def cstep_cond_def)
      apply(subst hd_conv_nth, erule COMP_noNil)
      apply fast+
  apply(erule bexE)
  apply(rule_tac x=sq' in bexI)
   apply simp
  apply(clarsimp simp: EnvCond_def pcs_def)
  done




theorem prog_corr_RG :
"\<rho>, \<rho>' \<Turnstile> p \<sqsupseteq>\<^bsub>r\<^esub> p' \<Longrightarrow> 
 \<rho> \<Turnstile> {R, P} p {Q, G} \<Longrightarrow>
 r O R' \<subseteq> R O r \<Longrightarrow>
 P' \<subseteq> r `` P \<Longrightarrow>
 r `` Q \<subseteq> Q' \<Longrightarrow>
 r\<inverse> O G O r \<subseteq> G' \<Longrightarrow>
 \<rho>' \<Turnstile> {R', P'} p' {Q', G'}"
  apply(subst HoareTripleRG_def, clarify)
  apply(rename_tac sq)
  apply(clarsimp simp: InitCond_def)
  apply(subgoal_tac "c=p'", clarify)
   apply(subst (asm) hd_conv_nth, erule pcs_noNil)
   apply(drule subsetD, assumption, clarify)
   apply(drule prog_corr_sq_replay, assumption+)
   apply clarsimp
   apply(subst (asm) HoareTripleRG_def)
   apply(subgoal_tac "sq' \<in> \<lbrakk>p\<rbrakk>\<^sub>\<rho>")
   apply(drule_tac c=sq' in subsetD, simp add: InitCond_def)
     apply(rule conjI, erule exI)
     apply(subst hd_conv_nth, erule pcs_noNil)
     apply simp
    apply clarify
    apply(rule conjI)
     apply(subst TermCond_def, simp)
     apply(rule conjI, erule exI)
     apply clarify
     apply(frule_tac x=j in spec, drule mp, simp)
     apply clarsimp
     apply(drule prog_corr_skipD2)
     apply(drule_tac TermCond_D)
     apply(drule_tac x=j in spec, drule mp, simp, drule mp, assumption)
     apply clarsimp
     apply(drule_tac x=i in spec, drule mp, simp)
     apply clarsimp
     apply(drule prog_corr_skipD1)
     apply(drule_tac c="stateOf (sq ! i)" in subsetD, erule ImageI, assumption)
     apply(rule_tac x=i in exI, simp)
     apply(case_tac "sq!i", clarsimp)
    apply(subst ProgCond_def, simp)
    apply(rule conjI, erule exI)
    apply(clarsimp simp: cstep_cond_def)
    apply(drule_tac t="sq ! (i - Suc 0)" in sym)
    apply(case_tac "sq'!(i-1)", clarsimp)
    apply(rename_tac p0 s0 tk0)
    apply(case_tac "sq'!i", clarsimp)
    apply(rename_tac p1 s1 tk1)
    apply(frule_tac x="i-1" in spec, drule_tac P="i-1<length sq'" in mp, simp)
    apply(drule_tac x=i in spec, drule mp, assumption)
    apply clarsimp
    apply(drule_tac i=i in ProgCond_D, assumption+)
    apply(erule subsetD)
    apply fast
   apply(clarsimp simp: EnvCond_def pcs_def)
   apply(subst (asm) hd_conv_nth, erule COMP_noNil)+
   apply simp
  apply(clarsimp simp: pcs_def)
  done



corollary prog_corr_RG_sub :
"\<rho>, \<rho>' \<Turnstile> p \<sqsupseteq> p' \<Longrightarrow> 
 \<rho> \<Turnstile> {R, P} p {Q, G} \<Longrightarrow>
 \<rho>' \<Turnstile> {R, P} p' {Q, G}"
  by(erule prog_corr_RG, assumption, clarsimp+)


corollary prog_corr_RG_eq :
"\<rho>, \<rho>' \<Turnstile> p \<approx> p' \<Longrightarrow> 
 (\<rho> \<Turnstile> {R, P} p {Q, G}) = (\<rho>' \<Turnstile> {R, P} p' {Q, G})"
  apply(clarsimp simp: small_step_eqv)
  apply(rule iffI)
   apply(erule prog_corr_RG_sub, assumption)+
  done



corollary ConseqRG: 
"\<rho> \<Turnstile> {R, S} p {Q, G}  \<Longrightarrow> 
 R' \<subseteq> R \<Longrightarrow> S' \<subseteq> S \<Longrightarrow> Q \<subseteq> Q' \<Longrightarrow> G \<subseteq> G' \<Longrightarrow>
 \<rho> \<Turnstile> {R', S'} p {Q', G'}"
  apply(rule_tac r=Id in prog_corr_RG)
       apply(rule prog_corr_refl)
      apply assumption
  by fast+




section "Plain syntax-directed tactic for program correspondences"

lemma PCasesE :
"i < Suc n \<Longrightarrow> (i = n \<Longrightarrow> P i) \<Longrightarrow> (i < n \<Longrightarrow> P i) \<Longrightarrow> P i" 
by(erule Nat.less_SucE, simp_all)

lemma PCasesE' :
"i < Suc n \<Longrightarrow> P n \<Longrightarrow> (i < n \<Longrightarrow> P i) \<Longrightarrow> P i" 
by(erule PCasesE, simp_all)

ML \<open>

fun rts ctxt t i =
  resolve_tac ctxt t i

fun rt ctxt t i =
  resolve_tac ctxt [t] i

fun et ctxt t i =
  eresolve_tac ctxt [t] i

fun dt ctxt t i =
  dresolve_tac ctxt [t] i


fun PlainProgCorrTac props ctxt i =
FIRST[rt ctxt (@{thm ProgCorr.prog_corr_seqs}) i,
      ((rt ctxt (@{thm ProgCorr.prog_corr_scheme})) THEN_ALL_NEW clarsimp_tac ctxt) i,
      ((rt ctxt (@{thm ProgCorr.prog_corr_parallels'})) THEN_ALL_NEW clarsimp_tac ctxt) i,
      rt ctxt (@{thm ProgCorr.prog_corr_whiles}) i,
      rt ctxt (@{thm ProgCorr.prog_corr_conds}) i,
      rt ctxt (@{thm ProgCorr.prog_corr_cjumps}) i,
        rt ctxt (@{thm ProgCorr.prog_corr_atomic2_basic}) i,
        rt ctxt (@{thm ProgCorr.prog_corr_atomic3_basic}) i,
      rt ctxt (@{thm ProgCorr.prog_corr_await_basic}) i, 
      ((rt ctxt (@{thm ProgCorr.prog_corr_basics})) THEN_ALL_NEW clarsimp_tac ctxt) i,
      rt ctxt (@{thm ProgCorr.prog_corr_skips}) i,
      (et ctxt (@{thm PCasesE'}) i) THEN (safe_simp_tac ctxt i),
       rts ctxt props i
]


fun plain_prog_corr_tac props ctxt =
 SUBGOAL (fn (_, i) => REPEAT_ALL_NEW (PlainProgCorrTac props ctxt) i THEN TRYALL (clarsimp_tac ctxt)) 

val _ =
  Theory.setup
    (Method.setup @{binding plain_prog_corr_tac} (Attrib.thms >> (fn ths => fn ctxt => 
      SIMPLE_METHOD' (plain_prog_corr_tac ths ctxt)))
      "Plain syntax-directed tactic for the program correspondences")

\<close>


end