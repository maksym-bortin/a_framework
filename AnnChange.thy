(* *********************************************************************

    Theory AnnChange.thy is part of a framework for modelling,
    verification and transformation of concurrent imperative
    programs. Copyright (c) 2021  M. Bortin

    The framework is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.
    For more details see the license agreement (LICENSE) you should have
    received along with the framework.
    
   ******************************************************************* *)

theory AnnChange 
imports ProgCorr
begin


inductive_set Eq_upto_ann :: "('s LA \<times> 's LA) set"
where "(Skip, Skip) \<in> Eq_upto_ann" |
      "(Basic f, Basic f) \<in> Eq_upto_ann" |
      "(p, p') \<in> Eq_upto_ann \<Longrightarrow> (q, q') \<in> Eq_upto_ann \<Longrightarrow>
       (IF C THEN p ELSE q FI, 
        IF C THEN p' ELSE q' FI) \<in> Eq_upto_ann" |
      "(p, p') \<in> Eq_upto_ann \<Longrightarrow> (q, q') \<in> Eq_upto_ann \<Longrightarrow>
       (WHILE C \<lbrakk>inv: I\<rbrakk> DO p SUBSEQUENTLY q OD, 
        WHILE C \<lbrakk>inv: I'\<rbrakk> DO p' SUBSEQUENTLY q' OD) \<in> Eq_upto_ann" |
      "(p, p') \<in> Eq_upto_ann \<Longrightarrow> (q, q') \<in> Eq_upto_ann \<Longrightarrow>
       (p;q, p';q') \<in> Eq_upto_ann" |
      "(p, p') \<in> Eq_upto_ann \<Longrightarrow> 
       (AWAIT C \<lbrakk>ann: a\<rbrakk> THEN p END, AWAIT C \<lbrakk>ann: a'\<rbrakk> THEN p' END) \<in> Eq_upto_ann" |
      "(Parallel [], Parallel []) \<in> Eq_upto_ann" |
      "(p, p') \<in> Eq_upto_ann \<Longrightarrow> (Parallel ps, Parallel ps') \<in> Eq_upto_ann \<Longrightarrow> 
       (Parallel ((p, a)#ps), Parallel ((p', a')#ps')) \<in> Eq_upto_ann"



lemma Eq_upto_ann_Parallels :
"(Parallel ps, Parallel ps') \<in> Eq_upto_ann \<Longrightarrow> i < length ps \<Longrightarrow>
  (fst (ps ! i), fst (ps' ! i)) \<in> Eq_upto_ann"
  apply(induct i arbitrary:ps ps')
   apply(erule Eq_upto_ann.cases, simp_all)+
  done

lemma Eq_upto_ann_ParallelsI :
"\<forall>i<length ps. (fst (ps ! i), fst (ps' ! i)) \<in> Eq_upto_ann \<Longrightarrow>
 length ps = length ps' \<Longrightarrow>
 (Parallel ps, Parallel ps') \<in> Eq_upto_ann"
  apply(induct ps arbitrary:ps')
   apply clarsimp
   apply(rule Eq_upto_ann.intros)
  apply clarsimp
  apply(case_tac ps', clarsimp+)
  apply(rule Eq_upto_ann.intros)
   apply(drule_tac x=0 in spec, simp)
  apply fastforce
  done


lemma Eq_upto_ann_scheme[simp] :
"(\<And>i. n\<le>i \<Longrightarrow> i<m \<Longrightarrow> (fst(f i), fst(g i)) \<in> Eq_upto_ann) \<Longrightarrow> 
 (Parallel (map f [n..<m]), Parallel (map g [n..<m])) \<in> Eq_upto_ann"
  by(rule Eq_upto_ann_ParallelsI, simp_all)


lemma Eq_upto_ann_Parallels_len :
"(Parallel ps, Parallel ps') \<in> Eq_upto_ann \<Longrightarrow>
 length ps = length ps'"
  apply(induct ps arbitrary:ps')
   apply(erule Eq_upto_ann.cases, simp_all)+
  done

lemma Eq_upto_ann_await_aux :
"(\<lambda>x1 x2. \<rho> \<turnstile> x1 -p\<rightarrow> x2 \<and>
           (\<forall>q. (fst x1, q) \<in> Eq_upto_ann \<longrightarrow>
                (\<exists>q'. \<rho> \<turnstile> (q, snd x1) -p\<rightarrow> (q', snd x2) \<and> (fst x2, q') \<in> Eq_upto_ann)))\<^sup>*\<^sup>*
        cf cf' \<Longrightarrow>
  \<forall>q. (fst cf, q) \<in> Eq_upto_ann \<longrightarrow>
  (\<exists>q'. \<rho> \<turnstile> (q, snd cf) -p\<rightarrow>\<^sup>* (q', snd cf') \<and> (fst cf', q') \<in> Eq_upto_ann)"
  apply(erule converse_rtranclp_induct)
  apply clarify
  apply(rule_tac x=q in exI, simp)
  apply clarsimp
  apply(drule spec, drule mp, assumption)
  apply clarify
  apply(drule spec, drule mp, assumption)
  apply clarify
  apply(rule exI, rule conjI, rule rtranclp_trans)
   apply(erule r_into_rtranclp)
  apply assumption+
  done


lemma Eq_upto_ann_sym :
"(p, q) \<in> Eq_upto_ann \<Longrightarrow> (q, p) \<in> Eq_upto_ann"
  apply(induct rule: Eq_upto_ann.induct)
         apply(rule Eq_upto_ann.intros)+
        apply assumption+
      apply(rule Eq_upto_ann.intros, assumption+)+
   apply(rule Eq_upto_ann.intros)+
   apply assumption+
  done


lemma upto_ann_corr_aux[rule_format] :
"\<rho> \<turnstile> cf -p\<rightarrow> cf' \<Longrightarrow>
 (\<forall>q. (fst cf, q) \<in> Eq_upto_ann \<longrightarrow>
 (\<exists>q'. \<rho> \<turnstile> (q, snd cf) -p\<rightarrow> (q', snd cf') \<and> (fst cf', q') \<in> Eq_upto_ann))"
  apply(erule pstep.induct)
             apply clarsimp
             apply(erule Eq_upto_ann.cases, simp_all)
             apply(rule exI, rule conjI, rule pstep.Basic)
             apply(rule Eq_upto_ann.intros)
            apply clarsimp
            apply(erule Eq_upto_ann.cases, simp_all)
           apply clarsimp
           apply(erule Eq_upto_ann.cases, simp_all)
          apply clarsimp
          apply(erule Eq_upto_ann.cases, simp_all)
          apply clarify
          apply(drule spec, drule mp, assumption)
          apply clarify
          apply(rule exI, rule conjI, erule pstep.Seq)
          apply(erule Eq_upto_ann.intros, assumption)
         apply clarsimp
         apply(erule Eq_upto_ann.cases, simp_all)
         apply clarify
         apply(erule Eq_upto_ann.cases, simp_all)
         apply clarify
         apply(rule exI, rule conjI, rule pstep.SeqSkip)
         apply assumption
        apply clarsimp
        apply(erule Eq_upto_ann.cases, simp_all)
        apply clarify
        apply(rule exI, rule conjI, erule pstep.CondT)
        apply assumption
       apply clarsimp
       apply(erule Eq_upto_ann.cases, simp_all)
       apply clarify
       apply(rule exI, rule conjI, erule pstep.CondF)
       apply assumption
      apply clarsimp
      apply(erule Eq_upto_ann.cases, simp_all)
      apply clarify
      apply(rule exI, rule conjI, erule pstep.WhileT)
      apply(rule Eq_upto_ann.intros, assumption)
      apply(rule Eq_upto_ann.intros)+
       apply assumption+
     apply clarsimp
     apply(erule Eq_upto_ann.cases, simp_all)
     apply clarify
     apply(rule exI, rule conjI, erule pstep.WhileF)
     apply assumption
    apply clarsimp
    apply(erule Eq_upto_ann.cases, simp_all)
    apply clarify
    apply(case_tac i, clarsimp)
     apply(drule spec, drule mp, assumption)
     apply clarify
     apply(rule exI, rule conjI, rule_tac i=0 in pstep.Parallel, simp, simp)
     apply simp
     apply(erule Eq_upto_ann.intros, assumption)
    apply clarsimp
    apply(rename_tac i)
    apply(drule_tac x="fst (ps'!i)" in spec)
    apply(drule mp)
     apply(erule Eq_upto_ann_Parallels, assumption)
    apply clarsimp
    apply(rule exI, rule conjI, rule_tac i="Suc i" in pstep.Parallel)
      apply simp
     apply(drule Eq_upto_ann_Parallels_len, simp)
    apply simp
    apply(erule Eq_upto_ann.intros)
    apply(frule Eq_upto_ann_Parallels_len)
    apply(rule Eq_upto_ann_ParallelsI)
     apply clarsimp
     apply(rename_tac j)
     apply(case_tac "i = j", simp)
     apply simp
     apply(erule Eq_upto_ann_Parallels, simp)
    apply simp
   apply clarsimp
   apply(erule Eq_upto_ann.cases, simp_all)
    apply clarify
    apply(rule exI, rule conjI, rule pstep.ParallelSkip, simp)
    apply(rule Eq_upto_ann.intros)
   apply clarsimp
   apply(erule Eq_upto_ann.cases, simp_all)
   apply(rule exI, rule conjI, rule pstep.ParallelSkip, simp)
    apply clarsimp
    apply(drule mem_nth)
    apply clarify
    apply(frule Eq_upto_ann_Parallels_len)
    apply(drule Eq_upto_ann_Parallels, simp)
    apply(drule bspec, rule_tac n=i in nth_mem, simp)
    apply(erule Eq_upto_ann.cases, simp_all)
    apply(drule sym, simp)
   apply(rule Eq_upto_ann.intros)
  apply clarsimp
  apply(erule Eq_upto_ann.cases, simp_all)
  apply clarify
  apply(drule Eq_upto_ann_await_aux)
  apply simp
  apply(drule spec, drule mp, assumption)
  apply clarify
  apply(thin_tac "_ \<in> Eq_upto_ann")
  apply(erule Eq_upto_ann.cases, simp_all)
  apply clarify
  apply(rule exI, rule conjI, erule pstep.Await, assumption)
  by(rule Eq_upto_ann.intros)



lemma upto_ann_corr :
"(p, q) \<in> Eq_upto_ann \<Longrightarrow>
 \<rho> \<Turnstile> p \<sqsupseteq> q"
  apply(simp add: prog_corr_def)
  apply(rule_tac x="Eq_upto_ann" in exI, simp)
  apply(simp add: prog_corrC_def)
  apply(rule conjI, clarsimp)
   apply(drule upto_ann_corr_aux)
    apply simp
    apply(erule Eq_upto_ann_sym)
   apply clarsimp
   apply(rule exI, erule conjI)
   apply(erule Eq_upto_ann_sym)
  apply(thin_tac "(p, q) \<in> Eq_upto_ann")
  apply(rule conjI, clarify)
   apply(erule Eq_upto_ann.cases, simp_all)
  apply clarify
  apply(erule Eq_upto_ann.cases, simp_all)
  done


lemma upto_ann_eqv :
"(p, q) \<in> Eq_upto_ann \<Longrightarrow>
 \<rho> \<Turnstile> p \<approx> q"
  apply(simp add: prog_mucorr_def)
  apply(rule conjI)
   apply(erule upto_ann_corr)
  apply(rule upto_ann_corr)   
  apply(erule Eq_upto_ann_sym)
  done


lemmas Eq_upto_ann1 = upto_ann_eqv[THEN prog_corr_RG_eq]


end